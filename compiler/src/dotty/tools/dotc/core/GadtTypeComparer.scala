package dotty.tools
package dotc
package core

import Constants.*, Contexts.*, Decorators.*, Denotations.*, Flags.*
import Names.*, NameOps.*, StdNames.*, Symbols.*, Types.*, TypeApplications.*, Variances.*
import cc.{CapturingType, CaptureSet, stripCapturing, isBoxedCapturing, boxed, boxedUnlessFun, boxedIfTypeParam, isAlwaysPure}
import config.*, Feature.migrateTo3, Printers.gadts
import reporting.trace
import transform.*, SymUtils.*, TypeUtils.*
import TypeComparer.{ ApproxState, AnyConstantType }

import scala.annotation.constructorOnly
import scala.collection.mutable
import scala.util.control.NonFatal

final class GadtTypeComparer(private val myContext: Context) extends PatternTypeConstrainer {
  protected given given_Context[DummySoItsADef]: Context = myContext
  def constraint: Constraint            = ctx.typerState.constraint
  def constraint_=(c: Constraint): Unit = ctx.typerState.constraint = c

  protected def rollbackUnless(op: => Boolean): Boolean =
    val saved = constraint
    var success = false
    try success = op
    finally if !success then constraint = saved
    success

  private var approx: ApproxState       = ApproxState.Fresh
  private var leftRoot: Type | Null     = _
  private var joined: Boolean           = false
  private var canCompareAtoms: Boolean  = true
  private var frozenGadt: Boolean       = false
  private var frozenConstraint: Boolean = false

  private inline def isSubTypeWhenFrozen(tp1: Type, tp2: Type)     = inFrozenConstraint(isSubType(tp1, tp2))
  private inline def inFrozenGadtAndConstraint[T](inline op: T): T = inFrozenGadtIf(true)(inFrozenConstraint(op))
  private inline def inFrozenGadt[T](inline op: T): T              = inFrozenGadtIf(true)(op)

  private inline def inFrozenConstraint[T](inline op: T): T =
    val saved = frozenConstraint
    frozenConstraint = true
    try op
    finally frozenConstraint = saved

  private inline def inFrozenGadtIf[T](cond: Boolean)(inline op: T): T =
    val saved = frozenGadt
    frozenGadt ||= cond
    try op finally frozenGadt = saved

  extension (sym: Symbol) private inline def onGadtBounds(inline op: TypeBounds => Boolean): Boolean =
    val bounds = ctx.gadt.bounds(sym)
    bounds != null && op(bounds)

  protected def isSubType(tp1: Type, tp2: Type): Boolean = isSubType(tp1, tp2, ApproxState.Fresh)
  private def isSubType(tp1: Type, tp2: Type, a: ApproxState): Boolean = {
    val savedApprox = approx
    val savedLeftRoot = leftRoot
    if a == ApproxState.Fresh then
      this.approx = ApproxState.None
      this.leftRoot = tp1
    else this.approx = a
    try recur(tp1, tp2)
    catch case ex: Throwable => handleRecursive("subtype", i"$tp1 <:< $tp2", ex, weight = 2)
    finally
      this.approx = savedApprox
      this.leftRoot = savedLeftRoot
  }

  private def recur(tp1: Type, tp2: Type): Boolean = trace(i"isSubType ${traceInfo(tp1, tp2)}$approx", subtyping) {

    def firstTry: Boolean = tp2 match {
      case tp2: NamedType =>
        def compareNamed(tp1: Type, tp2: NamedType): Boolean =
          given ctx: Context = myContext // optimization for performance
          val info2 = tp2.info

          /** Does `tp2` have a stable prefix?
           *  If that's not the case, following an alias via asSeenFrom could be lossy
           *  so we should not conclude `false` if comparing aliases fails.
           *  See pos/i17064.scala for a test case
           */
          def hasStablePrefix(tp: NamedType) =
            tp.prefix.isStable

          info2 match
            case info2: TypeAlias =>
              if recur(tp1, info2.alias) then return true
              if tp2.asInstanceOf[TypeRef].canDropAlias && hasStablePrefix(tp2) then
                return false
            case _ =>
          tp1 match
            case tp1: NamedType =>
              tp1.info match {
                case info1: TypeAlias =>
                  if recur(info1.alias, tp2) then return true
                  if tp1.asInstanceOf[TypeRef].canDropAlias && hasStablePrefix(tp2) then
                    return false
                case _ =>
              }
              val sym2 = tp2.symbol
              var sym1 = tp1.symbol
              if (sym1.is(ModuleClass) && sym2.is(ModuleVal))
                // For convenience we want X$ <:< X.type
                // This is safe because X$ self-type is X.type
                sym1 = sym1.companionModule
              if (sym1 ne NoSymbol) && (sym1 eq sym2) then
                ctx.erasedTypes ||
                sym1.isStaticOwner ||
                isSubPrefix(tp1.prefix, tp2.prefix) ||
                thirdTryNamed(tp2)
              else
                (  (tp1.name eq tp2.name)
                && !sym1.is(Private)
                && tp2.isPrefixDependentMemberRef
                && isSubPrefix(tp1.prefix, tp2.prefix)
                && tp1.signature == tp2.signature
                && !(sym1.isClass && sym2.isClass)  // class types don't subtype each other
                ) ||
                thirdTryNamed(tp2)
            case _ =>
              secondTry
        end compareNamed
        // See the documentation of `FromJavaObjectSymbol`
        if !ctx.erasedTypes && tp2.isFromJavaObject then
          recur(tp1, defn.AnyType)
        else
          compareNamed(tp1, tp2)
      case tp2: BoundType =>
        tp2 == tp1 || secondTry
      case tp2: TypeVar =>
        recur(tp1, tp2.underlying)
      case tp2: WildcardType =>
        def compareWild = tp2.optBounds match {
          case TypeBounds(_, hi) => recur(tp1, hi)
          case NoType => true
        }
        compareWild
      case tp2: LazyRef =>
        tp1.widen.isRef(defn.NothingClass) || !tp2.evaluating && recur(tp1, tp2.ref)
      case CapturingType(_, _) =>
        secondTry
      case tp2: AnnotatedType if !tp2.isRefining =>
        recur(tp1, tp2.parent)
      case tp2: ThisType =>
        def compareThis = {
          val cls2 = tp2.cls
          tp1 match {
            case tp1: ThisType =>
              tp1.cls eq cls2
            case tp1: NamedType if cls2.is(Module) && cls2.eq(tp1.typeSymbol) =>
              cls2.isStaticOwner ||
              recur(tp1.prefix, cls2.owner.thisType) ||
              secondTry
            case _ =>
              secondTry
          }
        }
        compareThis
      case tp2: SuperType =>
        def compareSuper = tp1 match {
          case tp1: SuperType =>
            recur(tp1.thistpe, tp2.thistpe) &&
            isSameType(tp1.supertpe, tp2.supertpe)
          case _ =>
            secondTry
        }
        compareSuper
      case AndType(tp21, tp22) =>
        recur(tp1, tp21) && recur(tp1, tp22)
      case OrType(tp21, tp22) =>
        if (tp21.stripTypeVar eq tp22.stripTypeVar) recur(tp1, tp21)
        else secondTry
      case TypeErasure.ErasedValueType(tycon1, underlying2) =>
        def compareErasedValueType = tp1 match {
          case TypeErasure.ErasedValueType(tycon2, underlying1) =>
            (tycon1.symbol eq tycon2.symbol) && isSubType(underlying1, underlying2)
          case _ =>
            secondTry
        }
        compareErasedValueType
      case ConstantType(v2) =>
        tp1 match {
          case ConstantType(v1) => v1.value == v2.value && recur(v1.tpe, v2.tpe)
          case _ => secondTry
        }
      case tp2: AnyConstantType =>
        if (tp2.tpe.exists) recur(tp1, tp2.tpe)
        else tp1 match {
          case tp1: ConstantType =>
            tp2.tpe = tp1
            true
          case _ =>
            secondTry
        }
      case _: FlexType =>
        true
      case _ =>
        secondTry
    }

    def secondTry: Boolean = tp1 match {
      case tp1: NamedType =>
        tp1.info match {
          case info1: TypeAlias =>
            if (recur(info1.alias, tp2)) return true
            if (tp1.prefix.isStable) return tryLiftedToThis1
          case _ =>
            if (tp1 eq defn.NothingType) || tp1.widen.isRef(defn.NothingClass) then return true
        }
        thirdTry
      case tp1: TypeParamRef =>
        def flagNothingBound = {
          if (!frozenConstraint && tp2.widen.isRef(defn.NothingClass) && ctx.typerState.isGlobalCommittable) {
            def msg = s"!!! instantiated to Nothing: $tp1, constraint = ${constraint.show}"
            if (Config.failOnInstantiationToNothing) assert(false, msg)
            else report.log(msg)
          }
          true
        }
        def compareTypeParamRef =
           tp2.dealias.match {
              case tp2a: TypeParamRef => constraint.isLess(tp1, tp2a)
              case tp2a: AndType => recur(tp1, tp2a)
              case _ => false
          }
          || isSubTypeWhenFrozen(constraint.bounds(tp1).hi.boxed, tp2)
          || (if canConstrain(tp1) && !approx.high then
                addConstraint(tp1, tp2, fromBelow = false) && flagNothingBound
              else thirdTry)

        compareTypeParamRef
      case tp1: ThisType =>
        val cls1 = tp1.cls
        tp2 match {
          case tp2: TermRef if cls1.is(Module) && cls1.eq(tp2.typeSymbol) =>
            cls1.isStaticOwner ||
            recur(cls1.owner.thisType, tp2.prefix) ||
            thirdTry
          case _ =>
            thirdTry
        }
      case tp1: SkolemType =>
        tp2 match {
          case tp2: SkolemType if !ctx.phase.isTyper && recur(tp1.info, tp2.info) => true
          case _ => thirdTry
        }
      case tp1: TypeVar =>
        recur(tp1.underlying, tp2)
      case tp1: WildcardType =>
        def compareWild = tp1.optBounds match {
          case bounds: TypeBounds => recur(bounds.lo, tp2)
          case _ => true
        }
        compareWild
      case tp1: LazyRef =>
        // If `tp1` is in train of being evaluated, don't force it
        // because that would cause an assertionError. Return false instead.
        // See i859.scala for an example where we hit this case.
        tp2.isRef(defn.AnyClass, skipRefined = false)
        || !tp1.evaluating && recur(tp1.ref, tp2)
      case AndType(tp11, tp12) =>
        if (tp11.stripTypeVar eq tp12.stripTypeVar) recur(tp11, tp2)
        else thirdTry
      case tp1 @ OrType(tp11, tp12) =>
        compareAtoms(tp1, tp2) match
          case Some(b) => return b
          case None =>

        def widenOK =
          (tp2.widenSingletons eq tp2)
          && (tp1.widenSingletons ne tp1)
          && inFrozenGadtAndConstraint(recur(tp1.widenSingletons, tp2))

        def joinOK = tp2.dealiasKeepRefiningAnnots match {
          case tp2: AppliedType if !tp2.tycon.typeSymbol.isClass =>
            // If we apply the default algorithm for `A[X] | B[Y] <: C[Z]` where `C` is a
            // type parameter, we will instantiate `C` to `A` and then fail when comparing
            // with `B[Y]`. To do the right thing, we need to instantiate `C` to the
            // common superclass of `A` and `B`.
            inFrozenGadtAndConstraint(recur(tp1.join, tp2))
          case _ =>
            false
        }

        /** Mark toplevel type vars in `tp2` as hard in the current constraint */
        def hardenTypeVars(tp2: Type): Unit = tp2.dealiasKeepRefiningAnnots match
          case tvar: TypeVar if constraint.contains(tvar.origin) =>
            constraint = constraint.withHard(tvar)
          case tp2: TypeParamRef if constraint.contains(tp2) =>
            hardenTypeVars(constraint.typeVarOfParam(tp2))
          case tp2: AndOrType =>
            hardenTypeVars(tp2.tp1)
            hardenTypeVars(tp2.tp2)
          case _ =>

        val res = widenOK || joinOK
          || recur(tp11, tp2) && recur(tp12, tp2)
          || containsAnd(tp1)
              && !joined
              && {
                joined = true
                try inFrozenGadt(recur(tp1.join, tp2))
                finally joined = false
              }
              // An & on the left side loses information. We compensate by also trying the join.
              // This is less ad-hoc than it looks since we produce joins in type inference,
              // and then need to check that they are indeed supertypes of the original types
              // under -Ycheck. Test case is i7965.scala.
              // On the other hand, we could get a combinatorial explosion by applying such joins
              // recursively, so we do it only once. See i14870.scala as a test case, which would
              // loop for a very long time without the recursion brake.

        if res && !tp1.isSoft && ctx.typerState.isCommittable then
          // We use a heuristic here where every toplevel type variable on the right hand side
          // is marked so that it converts all soft unions in its lower bound to hard unions
          // before it is instantiated. The reason is that the variable's instance type will
          // be a supertype of (decomposed and reconstituted) `tp1`.
          hardenTypeVars(tp2)

        res

      case CapturingType(parent1, refs1) =>
        if tp2.isAny then true
        else if subCaptures(refs1, tp2.captureSet) && sameBoxed(tp1, tp2, refs1)
          || !ctx.mode.is(Mode.CheckBoundsOrSelfType) && tp1.isAlwaysPure
        then recur(parent1, tp2)
        else thirdTry
      case tp1: AnnotatedType if !tp1.isRefining =>
        recur(tp1.parent, tp2)
      case tp1: MatchType =>
        val reduced = tp1.reduced
        if reduced.exists then recur(reduced, tp2)
        else thirdTry
      case _: FlexType =>
        true
      case _ =>
        thirdTry
    }

    def thirdTry: Boolean = tp2 match {
      case tp2 @ AppliedType(tycon2, args2) => compareAppliedType2(tp2, tycon2, args2)
      case tp2: NamedType                   => thirdTryNamed(tp2)
      case tp2: TypeParamRef                => compareTypeParamRef2(tp2)
      case tp2: RefinedType =>
        def compareRefinedSlow: Boolean =
          val name2 = tp2.refinedName
          recur(tp1, tp2.parent)
          && (name2 == nme.WILDCARD || hasMatchingMember(name2, tp1, tp2))

        def decomposeRefinements(tp: Type, refines: List[(Name, Type)]): Type = tp match
          case RefinedType(parent, rname, rinfo) =>
            decomposeRefinements(parent, (rname, rinfo) :: refines)
          case AndType(tp1, tp2) =>
            AndType(decomposeRefinements(tp1, refines), decomposeRefinements(tp2, refines))
          case _ =>
            refines.map(RefinedType(tp, _, _): Type).reduce(AndType(_, _))

        val tp1w = tp1.widen

        val skipped2 = skipMatching(tp1w, tp2)
        if skipped2 eq tp2 then
          if containsAnd(tp1) then
            tp2.parent match
              case _: RefinedType | _: AndType =>
                // maximally decompose RHS to limit the bad effects of the `either` that is necessary
                // since LHS contains an AndType
                recur(tp1, decomposeRefinements(tp2, Nil))
              case _ =>
                // Delay calling `compareRefinedSlow` because looking up a member
                // of an `AndType` can lead to a cascade of subtyping checks
                // This twist is needed to make collection/generic/ParFactory.scala compile
                fourthTry || compareRefinedSlow
          else if tp1.isInstanceOf[HKTypeLambda] then
            // HKTypeLambdas do not have members.
            fourthTry
          else
            compareRefinedSlow || fourthTry
        else // fast path, in particular for refinements resulting from parameterization.
          isSubRefinements(tp1w.asInstanceOf[RefinedType], tp2, skipped2) &&
          recur(tp1, skipped2)

      case tp2: RecType => tp1.safeDealias match
          case tp1: RecType =>
            val rthis1 = tp1.recThis
            recur(tp1.parent, tp2.parent.substRecThis(tp2, rthis1))
          case NoType => false
          case _ =>
            val tp1stable = ensureStableSingleton(tp1)
            recur(fixRecs(tp1stable, tp1stable.widenExpr), tp2.parent.substRecThis(tp2, tp1stable))
      case tp2: HKTypeLambda => tp1.stripTypeVar match
          case tp1: HKTypeLambda =>
            def boundsOK =
              migrateTo3 ||
              tp1.typeParams.corresponds(tp2.typeParams)((tparam1, tparam2) =>
                isSubType(tparam2.paramInfo.subst(tp2, tp1), tparam1.paramInfo))
            val variancesOK = variancesConform(tp1.typeParams, tp2.typeParams)
            variancesOK && boundsOK && isSubType(tp1.resType, tp2.resType.subst(tp2, tp1))
          case _ =>
            val tparams1 = tp1.typeParams
            if (tparams1.nonEmpty)
              return recur(tp1.EtaExpand(tparams1), tp2) || fourthTry
            tp2 match {
              case EtaExpansion(tycon2: TypeRef) if tycon2.symbol.isClass && tycon2.symbol.is(JavaDefined) =>
                recur(tp1, tycon2) || fourthTry
              case _ =>
                fourthTry
            }
      case tp2 @ OrType(tp21, tp22) =>
        compareAtoms(tp1, tp2) match
          case Some(b) => return b
          case _ =>

        // The next clause handles a situation like the one encountered in i2745.scala.
        // We have:
        //
        //   x: A | B, x.type <:< A | X   where X is a type variable
        //
        // We should instantiate X to B instead of x.type or A | B. To do this, we widen
        // the LHS to A | B and recur *without indicating that this is a lowApprox*. The
        // latter point is important since otherwise we would not get to instantiate X.
        // If that succeeds, fine. If not we continue and hit the `either` below.
        // That second path is important to handle comparisons with unions of singletons,
        // as in `1 <:< 1 | 2`.
        val tp1w = tp1.widen
        if ((tp1w ne tp1) && recur(tp1w, tp2))
          return true

        val tp1a = tp1.dealiasKeepRefiningAnnots
        if (tp1a ne tp1)
          // Follow the alias; this might lead to an OrType on the left which needs to be split
          return recur(tp1a, tp2)

        // Rewrite T1 <: (T211 & T212) | T22 to T1 <: (T211 | T22) and T1 <: (T212 | T22)
        // and analogously for T1 <: T21 | (T221 & T222)
        // `|' types to the right of <: are problematic, because
        // we have to choose one constraint set or another, which might cut off
        // solutions. The rewriting delays the point where we have to choose.
        tp21 match {
          case AndType(tp211, tp212) =>
            return recur(tp1, OrType(tp211, tp22, tp2.isSoft)) && recur(tp1, OrType(tp212, tp22, tp2.isSoft))
          case _ =>
        }
        tp22 match {
          case AndType(tp221, tp222) =>
            return recur(tp1, OrType(tp21, tp221, tp2.isSoft)) && recur(tp1, OrType(tp21, tp222, tp2.isSoft))
          case _ =>
        }
        either(recur(tp1, tp21), recur(tp1, tp22)) || fourthTry
      case tp2: MatchType =>
        val reduced = tp2.reduced
        if reduced.exists then recur(tp1, reduced)
        else fourthTry
      case tp2: MethodType => tp1 match
          case tp1: MethodType =>
            (tp1.signature consistentParams tp2.signature) &&
            matchingMethodParams(tp1, tp2) &&
            (!tp2.isImplicitMethod || tp1.isImplicitMethod) &&
            isSubType(tp1.resultType, tp2.resultType.subst(tp2, tp1))
          case _ => false
      case tp2: PolyType => tp1 match
          case tp1: PolyType =>
            (tp1.signature consistentParams tp2.signature)
            && matchingPolyParams(tp1, tp2)
            && isSubType(tp1.resultType, tp2.resultType.subst(tp2, tp1))
          case _ => false
      case _ @ ExprType(restpe2) => tp1 match
          // We allow ()T to be a subtype of => T.
          // We need some subtype relationship between them so that e.g.
          // def toString   and   def toString()   don't clash when seen
          // as members of the same type. And it seems most logical to take
          // ()T <:< => T, since everything one can do with a => T one can
          // also do with a ()T by automatic () insertion.
          case tp1 @ MethodType(Nil) => isSubType(tp1.resultType, restpe2)
          case _ @ ExprType(restpe1) => isSubType(restpe1, restpe2)
          case _ => fourthTry
      case tp2 @ TypeBounds(lo2, hi2) => tp1 match
          case _ @ TypeBounds(lo1, hi1) =>
            ((lo2 eq defn.NothingType) || isSubType(lo2, lo1)) &&
            ((hi2 eq defn.AnyType) && !hi1.isLambdaSub
             || (hi2 eq defn.AnyKindType)
             || isSubType(hi1, hi2))
          case tp1: ClassInfo =>
            tp2 contains tp1
          case _ =>
            false
      case CapturingType(parent2, refs2) =>
        def compareCapturing =
          val refs1 = tp1.captureSet
          try
            if refs1.isAlwaysEmpty then recur(tp1, parent2)
            else subCaptures(refs1, refs2)
              && sameBoxed(tp1, tp2, refs1)
              && (recur(tp1.widen.stripCapturing, parent2)
                 || tp1.isInstanceOf[SingletonType] && recur(tp1, parent2)
                    // this alternative is needed in case the right hand side is a
                    // capturing type that contains the lhs as an alternative of a union type.
                 )
          catch case ex: AssertionError =>
            println(i"assertion failed while compare captured $tp1 <:< $tp2")
            throw ex
        compareCapturing || fourthTry
      case tp2: AnnotatedType if tp2.isRefining =>
        (tp1.derivesAnnotWith(tp2.annot.sameAnnotation) || tp1.isBottomType) &&
        recur(tp1, tp2.parent)
      case ClassInfo(pre2, cls2, _, _, _) => tp1 match
          case ClassInfo(pre1, cls1, _, _, _) =>
            (cls1 eq cls2) && isSubType(pre1, pre2)
          case _ =>
            false
      case _ =>
        fourthTry
    }

    def fourthTry: Boolean = tp1 match {
      case tp1: TypeRef =>
        tp1.info match {
          case TypeBounds(lo1, hi1) =>
            def compareGADT =
              tp1.symbol.onGadtBounds(gbounds1 =>
                isSubTypeWhenFrozen(gbounds1.hi, tp2)
                  || narrowGADTBounds(tp1, tp2, approx, isUpper = true))

            isSubType(hi1.boxedIfTypeParam(tp1.symbol), tp2, approx.addLow)
              || compareGADT
              || tryLiftedToThis1
          case _ =>
            def isNullable(tp: Type): Boolean = tp.widenDealias match
              case tp: TypeRef =>
                val tpSym = tp.symbol
                ctx.mode.is(Mode.RelaxedOverriding) && !tpSym.isPrimitiveValueClass ||
                  tpSym.isNullableClass
              case tp: RefinedOrRecType => isNullable(tp.parent)
              case tp: AppliedType => isNullable(tp.tycon)
              case AndType(tp1, tp2) => isNullable(tp1) && isNullable(tp2)
              case OrType(tp1, tp2) => isNullable(tp1) || isNullable(tp2)
              case AnnotatedType(tp1, _) => isNullable(tp1)
              case _ => false
            val sym1 = tp1.symbol
            (sym1 eq defn.NothingClass) && tp2.isValueTypeOrLambda ||
              (sym1 eq defn.NullClass) && isNullable(tp2)
        }
      case tp1 @ AppliedType(tycon1, args1) => compareAppliedType1(tp1, tycon1, args1)
      case tp1: SingletonType =>
        def comparePaths = tp2 match
          case tp2: TermRef =>
            compareAtoms(tp1, tp2, knownSingletons = true).getOrElse(false)
              || { // needed to make from-tasty work. test cases: pos/i1753.scala, pos/t839.scala
              tp2.info.widenExpr.dealias match
                case tp2i: SingletonType => recur(tp1, tp2i)
                case _ => false
            }
          case _ => false

        def tp1widened =
          val tp1w = tp1.underlying.widenExpr
          tp1 match
            case tp1: CaptureRef if tp1.isTracked =>
              CapturingType(tp1w.stripCapturing, tp1.singletonCaptureSet)
            case _ =>
              tp1w

        comparePaths || isSubType(tp1widened, tp2, approx.addLow)
      case tp1: RefinedType  => isNewSubType(tp1.parent)
      case tp1: RecType      => isNewSubType(tp1.parent)
      case tp1: HKTypeLambda => tp1 match
        case EtaExpansion(tycon1: TypeRef) if tycon1.symbol.isClass && tycon1.symbol.is(JavaDefined) => recur(tycon1, tp2)
        case _ => tp2 match
          case _: HKTypeLambda => false // this case was covered in thirdTry
          case _ => tp2.typeParams.hasSameLengthAs(tp1.paramRefs) && isSubType(tp1.resultType, tp2.appliedTo(tp1.paramRefs))
      case AndType(tp11, tp12) =>
        val tp2a = tp2.dealiasKeepRefiningAnnots
        if tp2a ne tp2 then // Follow the alias; this might avoid truncating the search space in the either below
          return recur(tp1, tp2a)

        tp11 match {
          case OrType(tp111, tp112) =>
            return recur(AndType(tp111, tp12), tp2) && recur(AndType(tp112, tp12), tp2)
          case _ =>
        }
        tp12 match {
          case OrType(tp121, tp122) =>
            return recur(AndType(tp11, tp121), tp2) && recur(AndType(tp11, tp122), tp2)
          case _ =>
        }
        //val tp1norm = simplifyAndTypeWithFallback(tp11, tp12, tp1) // TODO: dnw
        val tp1norm = TypeComparer.andType(tp11, tp12)
        if (tp1 ne tp1norm) recur(tp1norm, tp2)
        else either(recur(tp11, tp2), recur(tp12, tp2))
      case tp1: MatchType =>
        def compareMatch = tp2 match
          case tp2: MatchType =>
            isSameType(tp1.scrutinee, tp2.scrutinee) &&
              tp1.cases.corresponds(tp2.cases)(isSubType)
          case _ => false
        recur(tp1.underlying, tp2) || compareMatch
      case tp1: AnnotatedType if tp1.isRefining => isNewSubType(tp1.parent)
      case JavaArrayType(elem1) => tp2 match
          case JavaArrayType(elem2) => isSubType(elem1, elem2)
          case _ => tp2.isAnyRef
      case tp1: ExprType if ctx.phaseId > Phases.gettersPhase.id =>
        // getters might have converted T to => T, need to compensate.
        recur(tp1.widenExpr, tp2)
      case _ => false
    }

    def thirdTryNamed(tp2: NamedType): Boolean = tp2.info match {
      case info2: TypeBounds =>
        def compareGADT: Boolean =
          tp2.symbol.onGadtBounds(gbounds2 =>
            isSubTypeWhenFrozen(tp1, gbounds2.lo)
              || tp1.match {
              case tp1: NamedType if ctx.gadt.contains(tp1.symbol) =>
                // Note: since we approximate constrained types only with their non-param bounds,
                // we need to manually handle the case when we're comparing two constrained types,
                // one of which is constrained to be a subtype of another.
                // We do not need similar code in fourthTry, since we only need to care about
                // comparing two constrained types, and that case will be handled here first.
                ctx.gadt.isLess(tp1.symbol, tp2.symbol)
              case _ => false
            }
              || narrowGADTBounds(tp2, tp1, approx, isUpper = false))

        isSubApproxHi(tp1, info2.lo.boxedIfTypeParam(tp2.symbol))
          || compareGADT
          || tryLiftedToThis2
          || fourthTry

      case _ =>
        val cls2 = tp2.symbol
        if (cls2.isClass)
          if (cls2.typeParams.isEmpty) {
            if (cls2 eq defn.AnyKindClass) return true
            if (tp1.widen.isRef(defn.NothingClass)) return true
            if (tp1.isLambdaSub) return false
            // Note: We would like to replace this by `if (tp1.hasHigherKind)`
            // but right now we cannot since some parts of the standard library rely on the
            // idiom that e.g. `List <: Any`. We have to bootstrap without scalac first.
            if cls2 eq defn.AnyClass then return true
            if cls2 == defn.SingletonClass && tp1.isStable then return true
            return tryBaseType(cls2)
          }
          else if (cls2.is(JavaDefined)) {
            // If `cls2` is parameterized, we are seeing a raw type, so we need to compare only the symbol
            val base = nonExprBaseType(tp1, cls2)
            if (base.typeSymbol == cls2) return true
          }
          else if tp1.typeParams.nonEmpty && !tp1.isAnyKind then
            return recur(tp1, EtaExpansion(tp2))
        fourthTry
    }

    def compareTypeParamRef2(tp2: TypeParamRef): Boolean =
      val alwaysTrue =
        if frozenConstraint
        then recur(tp1, constraint.bounds(tp2).lo.boxed)
        else isSubTypeWhenFrozen(tp1, tp2)
      alwaysTrue
      || tp1.dealias.match { case tp1a: OrType => recur(tp1a, tp2) case _ => false }
      || (if canConstrain(tp2) && !approx.low then addConstraint(tp2, tp1.widenExpr, fromBelow = true) else fourthTry)

    def tryBaseType(cls2: Symbol) = {
      val base = nonExprBaseType(tp1, cls2).boxedIfTypeParam(tp1.typeSymbol)
      if base.exists && (base ne tp1) then
        isSubType(base, tp2, if (tp1.isRef(cls2)) approx else approx.addLow)
        || base.isInstanceOf[OrType] && fourthTry
          // if base is a disjunction, this might have come from a tp1 type that
          // expands to a match type. In this case, we should try to reduce the type
          // and compare the redux. This is done in fourthTry
      else fourthTry
    }

    def isSubPrefix(pre1: Type, pre2: Type): Boolean =
      def samePkg(sym1: Symbol, sym2: Symbol) =
           sym2.is(Package) && sym1.isPackageObject && sym1.owner == sym2.moduleClass
        || sym1.is(Package) && sym2.isPackageObject && sym2.owner == sym1.moduleClass
      pre1 match
        case pre1: ThisType =>
          pre2 match
            case pre2: ThisType =>
              if samePkg(pre1.cls, pre2.cls) then return true
              if pre1.cls.classInfo.selfType.derivesFrom(pre2.cls)
                 && pre2.cls.classInfo.selfType.derivesFrom(pre1.cls)
              then
                subtyping.println(i"assume equal prefixes $pre1 $pre2")
                return true
            case pre2: TermRef =>
              if samePkg(pre1.cls, pre2.symbol) then return true
            case _ =>
        case pre1: TermRef =>
          pre2 match
            case pre2: TermRef =>
              if samePkg(pre1.symbol, pre2.symbol) then return true
            case pre2: ThisType =>
              if samePkg(pre1.symbol, pre2.cls) then return true
            case _ =>
        case _ =>
      isSubType(pre1, pre2)
    end isSubPrefix

    def compareAppliedTypeParamRef(tycon: TypeParamRef, args: List[Type], other: AppliedType, fromBelow: Boolean): Boolean =
      def directionalIsSubType(tp1: Type, tp2: Type): Boolean =
        if fromBelow then isSubType(tp2, tp1) else isSubType(tp1, tp2)
      def directionalRecur(tp1: Type, tp2: Type): Boolean =
        if fromBelow then recur(tp2, tp1) else recur(tp1, tp2)

      val otherTycon = other.tycon
      val otherArgs = other.args

      val d = otherArgs.length - args.length
      d >= 0 && {
        val tparams = tycon.typeParams
        val remainingTparams = otherTycon.typeParams.drop(d)
        variancesConform(remainingTparams, tparams) && {
          val adaptedTycon =
            if d > 0 then
              val initialArgs = otherArgs.take(d)
              def bodyArgs(tl: HKTypeLambda) = initialArgs ++ tl.paramRefs
              def adaptedBounds(tl: HKTypeLambda) =
                val bodyArgsComputed = bodyArgs(tl)
                remainingTparams.map(_.paramInfo)
                  .mapconserve(_.substTypeParams(otherTycon, bodyArgsComputed).bounds)

              HKTypeLambda(remainingTparams.map(_.paramName))(
                adaptedBounds,
                tl => otherTycon.appliedTo(bodyArgs(tl)))
            else otherTycon
          directionalIsSubType(tycon, adaptedTycon)
          && directionalRecur(adaptedTycon.appliedTo(args), other)
        }
      }
    end compareAppliedTypeParamRef

    def compareAppliedType2(tp2: AppliedType, tycon2: Type, args2: List[Type]): Boolean = {
      val tparams = tycon2.typeParams
      if (tparams.isEmpty) return false // can happen for ill-typed programs, e.g. neg/tcpoly_overloaded.scala

      /** True if `tp1` and `tp2` have compatible type constructors and their
       *  corresponding arguments are subtypes relative to their variance (see `isSubArgs`).
       */
      def isMatchingApply(tp1: Type): Boolean = tp1.widen match {
        case tp1 @ AppliedType(tycon1, args1) =>
          // We intentionally do not automatically dealias `tycon1` or `tycon2` here.
          // `TypeApplications#appliedTo` already takes care of dealiasing type
          // constructors when this can be done without affecting type
          // inference, doing it here would not only prevent code from compiling
          // but could also result in the wrong thing being inferred later, for example
          // in `tests/run/hk-alias-unification.scala` we end up checking:
          //
          //   Foo[?F, ?T] <:< Foo[[X] =>> (X, String), Int]
          //
          // where
          //
          //   type Foo[F[_], T] = ErasedFoo[F[T]]
          //
          // Naturally, we'd like to infer:
          //
          //   ?F := [X] => (X, String)
          //
          // but if we dealias `Foo` then we'll end up trying to check:
          //
          //   ErasedFoo[?F[?T]] <:< ErasedFoo[(Int, String)]
          //
          // Because of partial unification, this will succeed, but will produce the constraint:
          //
          //   ?F := [X] =>> (Int, X)
          //
          // Which is not what we wanted!
          // On the other hand, we are not allowed to always stop at the present arguments either.
          // An example is i10129.scala. Here, we have the following situation:
          //
          //    type Lifted[A] = Err | A
          //    def point[O](o: O): Lifted[O] = o
          //    extension [O, U](o: Lifted[O]) def map(f: O => U): Lifted[U] = ???
          //    point("a").map(_ => if true then 1 else error)
          //
          // This leads to the constraint Lifted[U] <: Lifted[Int]. If we just
          // check the arguments this gives `U <: Int`. But this is wrong. Dealiasing
          // `Lifted` gives `Err | U <: Err | Int`, hence it should be `U <: Err | Int`.
          //
          // So it's a conundrum. We need to check the immediate arguments for hk type inference,
          // but this could narrow the constraint too much. The solution is to also
          // check the constraint arising from the dealiased subtype test
          // in the case where isSubArgs adds a constraint. If that second constraint
          // is weaker than the first, we keep it in place of the first.
          // Note that if the isSubArgs test fails, we will proceed anyway by
          // dealising by doing a compareLower.
          def loop(tycon1: Type, args1: List[Type]): Boolean = tycon1 match {
            case tycon1: TypeParamRef =>
              (tycon1 == tycon2 ||
               canConstrain(tycon1) && isSubType(tycon1, tycon2)) &&
              isSubArgs(args1, args2, tp1, tparams)
            case tycon1: TypeRef =>
              tycon2 match {
                case tycon2: TypeRef =>
                  val tycon1sym = tycon1.symbol
                  val tycon2sym = tycon2.symbol

                  var touchedGADTs = false
                  var gadtIsInstantiated = false

                  extension (sym: Symbol)
                    inline private def byGadtBounds(inline op: TypeBounds => Boolean): Boolean =
                      touchedGADTs = true
                      sym.onGadtBounds(
                        b => op(b) && { gadtIsInstantiated = b.isInstanceOf[TypeAlias]; true })

                  def byGadtOrdering: Boolean =
                    ctx.gadt.contains(tycon1sym)
                    && ctx.gadt.contains(tycon2sym)
                    && ctx.gadt.isLess(tycon1sym, tycon2sym)

                  (
                    tycon1sym == tycon2sym && isSubPrefix(tycon1.prefix, tycon2.prefix)
                    || tycon1sym.byGadtBounds(b => isSubTypeWhenFrozen(b.hi, tycon2))
                    || tycon2sym.byGadtBounds(b => isSubTypeWhenFrozen(tycon1, b.lo))
                    || byGadtOrdering
                  ) && {
                    // There are two cases in which we can assume injectivity.
                    // First we check if either sym is a class.
                    // Then:
                    // 1) if we didn't touch GADTs, then both symbols are the same
                    //    (b/c of an earlier condition) and both are the same class
                    // 2) if we touched GADTs, then the _other_ symbol (class syms
                    //    cannot have GADT constraints), the one w/ GADT cstrs,
                    //    must be instantiated, making the two tycons equal
                    val tyconIsInjective =
                      (tycon1sym.isClass || tycon2sym.isClass)
                      && (!touchedGADTs || gadtIsInstantiated)

                    inFrozenGadtIf(!tyconIsInjective) {
                      if tycon1sym == tycon2sym && tycon1sym.isAliasType then
                        val preConstraint = constraint
                        isSubArgs(args1, args2, tp1, tparams)
                        && tryAlso(preConstraint, recur(tp1.superTypeNormalized, tp2.superTypeNormalized))
                      else
                        isSubArgs(args1, args2, tp1, tparams)
                    }
                  }
                case _ =>
                  false
              }
            case tycon1: TypeVar =>
              loop(tycon1.underlying, args1)
            case tycon1: AnnotatedType if !tycon1.isRefining =>
              loop(tycon1.underlying, args1)
            case _ =>
              false
          }
          loop(tycon1, args1)
        case _ =>
          false
      }

      /** `param2` can be instantiated to a type application prefix of the LHS
       *  or to a type application prefix of one of the LHS base class instances
       *  and the resulting type application is a supertype of `tp1`.
       */
      def canInstantiate(tycon2: TypeParamRef): Boolean = {
        def appOK(tp1base: Type) = tp1base match {
          case tp1base: AppliedType =>
            compareAppliedTypeParamRef(tycon2, args2, tp1base, fromBelow = true)
          case _ => false
        }

        val tp1w = tp1.widen
        appOK(tp1w) || tp1w.typeSymbol.isClass && {
          val classBounds = tycon2.classSymbols
          def liftToBase(bcs: List[ClassSymbol]): Boolean = bcs match {
            case bc :: bcs1 =>
              classBounds.exists(bc.derivesFrom) && appOK(nonExprBaseType(tp1, bc))
              || liftToBase(bcs1)
            case _ =>
              false
          }
          liftToBase(tp1w.baseClasses)
        }
      }

      /** Fall back to comparing either with `fourthTry` or against the lower
       *  approximation of the rhs.
       *  @param   tyconLo   The type constructor's lower approximation.
       */
      def fallback(tyconLo: Type) =
        either(fourthTry, isSubApproxHi(tp1, tyconLo.applyIfParameterized(args2)))

      /** Let `tycon2bounds` be the bounds of the RHS type constructor `tycon2`.
       *  Let `app2 = tp2` where the type constructor of `tp2` is replaced by
       *  `tycon2bounds.lo`.
       *  If both bounds are the same, continue with `tp1 <:< app2`.
       *  otherwise continue with either
       *
       *    tp1 <:< tp2    using fourthTry (this might instantiate params in tp1)
       *    tp1 <:< app2   using isSubType (this might instantiate params in tp2)
       */
      def compareLower(tycon2bounds: TypeBounds, tyconIsTypeRef: Boolean): Boolean =
        if ((tycon2bounds.lo `eq` tycon2bounds.hi) && !tycon2bounds.isInstanceOf[MatchAlias])
          if (tyconIsTypeRef) recur(tp1, tp2.superTypeNormalized)
          else isSubApproxHi(tp1, tycon2bounds.lo.applyIfParameterized(args2))
        else
          fallback(tycon2bounds.lo)

      def byGadtBounds: Boolean =
          tycon2 match
            case tycon2: TypeRef =>
              val tycon2sym = tycon2.symbol
              tycon2sym.onGadtBounds { bounds2 =>
                inFrozenGadt { compareLower(bounds2, tyconIsTypeRef = false) }
              }
            case _ => false

      tycon2 match {
        case param2: TypeParamRef =>
          isMatchingApply(tp1) ||
          canConstrain(param2) && canInstantiate(param2) ||
          compareLower(constraint.bounds(param2), tyconIsTypeRef = false)
        case tycon2: TypeRef =>
          isMatchingApply(tp1) ||
          byGadtBounds ||
          defn.isCompiletimeAppliedType(tycon2.symbol) && compareCompiletimeAppliedType(tp2, tp1, fromBelow = true) || {
            tycon2.info match {
              case info2: TypeBounds =>
                compareLower(info2, tyconIsTypeRef = true)
              case info2: ClassInfo =>
                tycon2.name.startsWith("Tuple") &&
                  defn.isTupleNType(tp2) && recur(tp1, tp2.toNestedPairs) ||
                tryBaseType(info2.cls)
              case _ =>
                fourthTry
            }
          } || tryLiftedToThis2

        case tv: TypeVar =>
          if tv.isInstantiated then
            recur(tp1, tp2.superType)
          else
            compareAppliedType2(tp2, tv.origin, args2)
        case tycon2: AnnotatedType if !tycon2.isRefining =>
          recur(tp1, tp2.superType)
        case tycon2: AppliedType =>
          fallback(tycon2.lowerBound)
        case _ =>
          false
      }
    }

    def compareAppliedType1(tp1: AppliedType, tycon1: Type, args1: List[Type]): Boolean =
      tycon1 match {
        case param1: TypeParamRef =>
          def canInstantiate = tp2 match {
            case tp2base: AppliedType =>
              compareAppliedTypeParamRef(param1, args1, tp2base, fromBelow = false)
            case _ =>
              false
          }
          canConstrain(param1) && canInstantiate
          || isSubType(constraint.bounds(param1).hi.applyIfParameterized(args1), tp2, approx.addLow)
        case tycon1: TypeRef =>
          val sym = tycon1.symbol

          def byGadtBounds: Boolean =
            sym.onGadtBounds { bounds1 =>
              inFrozenGadt { isSubType(bounds1.hi.applyIfParameterized(args1), tp2, approx.addLow) }
            }

          !sym.isClass && {
            defn.isCompiletimeAppliedType(sym) && compareCompiletimeAppliedType(tp1, tp2, fromBelow = false) ||
            recur(tp1.superTypeNormalized, tp2) ||
            tryLiftedToThis1
          } || byGadtBounds
        case _: TypeProxy => recur(tp1.superTypeNormalized, tp2)
        case _            => false
      }

    def compareS(tp: AppliedType, other: Type, fromBelow: Boolean): Boolean = tp.args match {
      case arg :: Nil =>
        def natValue(tp: Type): Option[Int] = constValue(tp) match
          case Some(Constant(n: Int)) if n >= 0 => Some(n)
          case _ => None

        def constValue(tp: Type): Option[Constant] =
          val ct = new AnyConstantType
          if isSubTypeWhenFrozen(tp, ct) then ct.tpe match
            case ConstantType(c) => Some(c)
            case _ => None
          else None

        natValue(arg) match
          case Some(n) if n != Int.MaxValue =>
            val succ = ConstantType(Constant(n + 1))
            if fromBelow then recur(other, succ) else recur(succ, other)
          case _ => natValue(other) match
            case Some(n) if n > 0 =>
              val pred = ConstantType(Constant(n - 1))
              if fromBelow then recur(pred, arg) else recur(arg, pred)
            case _ => false
      case _ => false
    }

    def compareCompiletimeAppliedType(tp: AppliedType, other: Type, fromBelow: Boolean): Boolean = {
      if defn.isCompiletime_S(tp.tycon.typeSymbol) then compareS(tp, other, fromBelow)
      else
        val folded = tp.tryCompiletimeConstantFold
        if fromBelow then recur(other, folded) else recur(folded, other)
    }

    def isNewSubType(tp1: Type): Boolean = (!isCovered(tp1) || !isCovered(tp2)) && isSubType(tp1, tp2, approx.addLow)

    def isSubApproxHi(tp1: Type, tp2: Type): Boolean =
      tp1.eq(tp2) || tp2.ne(defn.NothingType) && isSubType(tp1, tp2, approx.addHigh)

    def nonExprBaseType(tp: Type, cls: Symbol)(using Context): Type =
      if tp.isInstanceOf[ExprType] then NoType else tp.baseType(cls)

    def tryLiftedToThis1: Boolean = { val tp1a = liftToThis(tp1); (tp1a ne tp1) && recur(tp1a, tp2) }
    def tryLiftedToThis2: Boolean = { val tp2a = liftToThis(tp2); (tp2a ne tp2) && recur(tp1, tp2a) }
    def liftToThis(tp: Type): Type = {
      def findEnclosingThis(moduleClass: Symbol, from: Symbol): Type =
        if ((from.owner eq moduleClass) && from.isPackageObject && from.is(Opaque)) from.thisType
        else if (from.is(Package)) tp
        else if ((from eq moduleClass) && from.is(Opaque)) from.thisType
        else if (from eq NoSymbol) tp
        else findEnclosingThis(moduleClass, from.owner)

      tp match {
        case tp: TermRef if tp.symbol.is(Module) =>
          findEnclosingThis(tp.symbol.moduleClass, ctx.owner)
        case tp: TypeRef =>
          val pre1 = liftToThis(tp.prefix)
          if ((pre1 ne tp.prefix) && pre1.exists) tp.withPrefix(pre1) else tp
        case tp: ThisType if tp.cls.is(Package) =>
          findEnclosingThis(tp.cls, ctx.owner)
        case tp: AppliedType =>
          val tycon1 = liftToThis(tp.tycon)
          if (tycon1 ne tp.tycon) tp.derivedAppliedType(tycon1, tp.args) else tp
        case tp: TypeVar if tp.isInstantiated =>
          liftToThis(tp.inst)
        case tp: AnnotatedType =>
          val parent1 = liftToThis(tp.parent)
          if (parent1 ne tp.parent) tp.derivedAnnotatedType(parent1, tp.annot) else tp
        case _ =>
          tp
      }
    }

    if tp2 eq NoType then false
    else if tp1 eq tp2 then true
    else
      val savedCstr = constraint
      val savedGadt = ctx.gadt
      inline def restore() =
        constraint = savedCstr
        ctx.gadtState.restore(savedGadt)
      try
        val result = firstTry
        if !result then restore()
        result
      catch case NonFatal(ex) =>
        restore()
        throw ex
  }

  private def compareAtoms(tp1: Type, tp2: Type, knownSingletons: Boolean = false): Option[Boolean] =

    def canCompare(ts: Set[Type]) =
      ctx.phase.isTyper
      || !ts.exists(_.existsPart(_.isInstanceOf[SkolemType], StopAt.Static))

    def verified(result: Boolean): Boolean =
      if Config.checkAtomsComparisons then
        try
          canCompareAtoms = false
          val regular = recur(tp1, tp2)
          assert(result == regular,
            i"""Atoms inconsistency for $tp1 <:< $tp2
              |atoms predicted $result
              |atoms1 = ${tp1.atoms}
              |atoms2 = ${tp2.atoms}""")
        finally canCompareAtoms = true
      result

    tp2.atoms match
      case Atoms.Range(lo2, hi2) if canCompareAtoms && canCompare(hi2) =>
        tp1.atoms match
          case Atoms.Range(lo1, hi1) =>
            if hi1.subsetOf(lo2) || knownSingletons && hi2.size == 1 && hi1 == hi2 then
              Some(verified(true))
            else if !lo1.subsetOf(hi2) then
              Some(verified(false))
            else
              None
          case _ => Some(verified(recur(tp1, defn.NothingType)))
      case _ => None

  private def isSubArgs(args1: List[Type], args2: List[Type], tp1: Type, tparams2: List[ParamInfo]): Boolean = {
    def paramBounds(tparam: Symbol): TypeBounds =
      tparam.info.substApprox(tparams2.asInstanceOf[List[Symbol]], args2).bounds

    def recurArgs(args1: List[Type], args2: List[Type], tparams2: List[ParamInfo]): Boolean =
      if args1.isEmpty then args2.isEmpty
      else args2.nonEmpty && tparams2.nonEmpty && {
        val tparam = tparams2.head
        val v = tparam.paramVarianceSign

        def compareCaptured(arg2: Type) = tparam match
          case tparam: Symbol =>
            val leftr = leftRoot.nn
            if (leftr.isStable || ctx.isAfterTyper) && leftr.isValueType && leftr.member(tparam.name).exists
            then
              val captured = TypeRef(leftr, tparam)
              try isSubArg(captured, arg2)
              catch case _: TypeError => false
            else if v > 0 then isSubType(paramBounds(tparam).hi, arg2)
            else if v < 0 then isSubType(arg2, paramBounds(tparam).lo)
            else false
          case _ => false

        def isSubArg(arg1: Type, arg2: Type): Boolean = arg2 match
          case arg2: TypeBounds =>
            val arg1norm = arg1 match {
              case arg1: TypeBounds =>
                tparam match {
                  case tparam: Symbol => arg1 & paramBounds(tparam)
                  case _ => arg1 // This case can only arise when a hk-type is illegally instantiated with a wildcard
                }
              case _ => arg1
            }
            arg2.contains(arg1norm)
          case ExprType(arg2res)
          if ctx.phaseId > Phases.elimByNamePhase.id && !ctx.erasedTypes
               && defn.isByNameFunction(arg1.dealias) =>
            // ElimByName maps `=> T` to `()? => T`, but only in method parameters. It leaves
            // embedded `=> T` arguments alone. This clause needs to compensate for that.
            isSubArg(arg1.dealias.argInfos.head, arg2res)
          case _ =>
            arg1 match
              case arg1: TypeBounds =>
                CaptureSet.subCapturesRange(arg1, arg2)
                  // subCapturesRange is important for invariant arguments that get expanded
                  // to TypeBounds where each bound is obtained by adding a captureset variable
                  // to the argument type. If subCapturesRange returns true we know that arg1's'
                  // capture set can be unified with arg2's capture set, so it only remains to
                  // check the underlying types with `isSubArg`.
                  && isSubArg(arg1.hi.stripCapturing, arg2.stripCapturing)
                || compareCaptured(arg2)
              case ExprType(arg1res)
              if ctx.phaseId > Phases.elimByNamePhase.id && !ctx.erasedTypes
                   && defn.isByNameFunction(arg2.dealias) =>
                 isSubArg(arg1res, arg2.argInfos.head)
              case _ =>
                if v < 0 then isSubType(arg2, arg1)
                else if v > 0 then isSubType(arg1, arg2)
                else isSameType(arg2, arg1)

        isSubArg(args1.head.boxedUnlessFun(tp1), args2.head.boxedUnlessFun(tp1))
      } && recurArgs(args1.tail, args2.tail, tparams2.tail)

    recurArgs(args1, args2, tparams2)
  }

  private def fixRecs(anchor: SingletonType, tp: Type): Type = {
    def fix(tp: Type): Type = tp.stripTypeVar match
      case tp: RecType                            => fix(tp.parent).substRecThis(tp, anchor)
      case tp @ RefinedType(parent, rname, rinfo) => tp.derivedRefinedType(fix(parent), rname, rinfo)
      case tp: TypeParamRef                       => fixOrElse(constraint.bounds(tp).hi, tp)
      case tp: TypeProxy                          => fixOrElse(tp.superType, tp)
      case tp: AndType                            => tp.derivedAndType(fix(tp.tp1), fix(tp.tp2))
      case tp: OrType                             => tp.derivedOrType (fix(tp.tp1), fix(tp.tp2))
      case tp                                     => tp
    def fixOrElse(tp: Type, fallback: Type) =
      val tp1 = fix(tp)
      if tp1 ne tp then tp1 else fallback
    fix(tp)
  }

  private def tryAlso(preConstraint: Constraint, op: => Boolean): true =
    if constraint ne preConstraint then
      // check whether `op2` generates a weaker constraint than `op1`
      val leftConstraint = constraint
      constraint = preConstraint
      if !op || !subsumes(leftConstraint, constraint, preConstraint) then
        constraint = leftConstraint
    true

  protected def either(op1: => Boolean, op2: => Boolean): Boolean = necessaryEither(op1, op2)
  private def necessaryEither(op1: => Boolean, op2: => Boolean): Boolean =
    val preConstraint = constraint
    val preGadt       = ctx.gadt

    def allSubsumes(g1: GadtConstraint, g2: GadtConstraint, c1: Constraint, c2: Constraint): Boolean =
      subsumes(c1, c2, preConstraint) &&
      subsumes(g1.constraint, g2.constraint, preGadt.constraint)

    inline def restore(g: GadtConstraint, c: Constraint): Unit =
      constraint = c
      ctx.gadtState.restore(g)

    if op1 then
      val op1Constraint = constraint
      val op1Gadt       = ctx.gadt
      restore(preGadt, preConstraint)
      if op2 then
        if allSubsumes(op1Gadt, ctx.gadt, op1Constraint, constraint) then
          ()
        else if allSubsumes(ctx.gadt, op1Gadt, constraint, op1Constraint) then
          restore(op1Gadt, op1Constraint)
        else
          restore(preGadt, preConstraint)
      else
        restore(op1Gadt, op1Constraint)
      true
    else op2
  end necessaryEither

  private def containsAnd(tp: Type): Boolean = tp match
    case _: AndType => true
    case OrType(tp1, tp2) => containsAnd(tp1) || containsAnd(tp2)
    case tp: TypeParamRef => containsAnd(constraint.bounds(tp).hi)
    case tp: TypeRef => containsAnd(tp.info.hiBound) || tp.symbol.onGadtBounds(gbounds => containsAnd(gbounds.hi))
    case tp: TypeProxy => containsAnd(tp.superType)
    case _ => false

  private def hasMatchingMember(name: Name, tp1: Type, tp2: RefinedType): Boolean =
    trace(i"hasMatchingMember($tp1 . $name :? ${tp2.refinedInfo}), mbr: ${tp1.member(name).info}", subtyping) {

      def matchAbstractTypeMember(info1: Type): Boolean = info1 match {
        case TypeBounds(lo, hi) if lo ne hi =>
          tp2.refinedInfo match {
            case rinfo2: TypeBounds if tp1.isStable =>
              val ref1 = tp1.widenExpr.select(name)
              isSubType(rinfo2.lo, ref1) && isSubType(ref1, rinfo2.hi)
            case _ =>
              false
          }
        case _ => false
      }

      def sigsOK(symInfo: Type, info2: Type) =
        tp2.underlyingClassRef(refinementOK = true).member(name).exists
        || tp2.derivesFrom(defn.WithoutPreciseParameterTypesClass)
        || symInfo.isInstanceOf[MethodType]
            && symInfo.signature.consistentParams(info2.signature)

      def tp1IsSingleton: Boolean = tp1.isInstanceOf[SingletonType]

      def isSubInfo(info1: Type, info2: Type, symInfo: Type): Boolean =
        info2 match
          case info2: MethodType =>
            info1 match
              case info1: MethodType =>
                val symInfo1 = symInfo.stripPoly
                matchingMethodParams(info1, info2, precise = false)
                && isSubInfo(info1.resultType, info2.resultType.subst(info2, info1), symInfo1.resultType)
                && sigsOK(symInfo1, info2)
              case _ => inFrozenGadtIf(tp1IsSingleton) { isSubType(info1, info2) }
          case _ => inFrozenGadtIf(tp1IsSingleton) { isSubType(info1, info2) }

      def qualifies(m: SingleDenotation): Boolean =
        val info1 = m.info.widenExpr
        isSubInfo(info1, tp2.refinedInfo.widenExpr, m.symbol.info.orElse(info1))
        || matchAbstractTypeMember(m.info)
        || (tp1.isStable && isSubType(TermRef(tp1, m.symbol), tp2.refinedInfo))

      tp1.member(name) match // inlined hasAltWith for performance
        case mbr: SingleDenotation => qualifies(mbr)
        case mbr => mbr hasAltWith qualifies
    }

  private def ensureStableSingleton(tp: Type): SingletonType = tp.stripTypeVar match {
    case tp: SingletonType if tp.isStable => tp
    case tp: ValueType => SkolemType(tp)
    case tp: TypeProxy => ensureStableSingleton(tp.superType)
    case tp => assert(ctx.reporter.errorsReported); SkolemType(tp)
  }

  private def skipMatching(tp1: Type, tp2: RefinedType): Type = tp1 match {
    case RefinedType(parent1, name1, _: TypeAlias) if name1 == tp2.refinedName =>
      tp2.parent match {
        case parent2: RefinedType => skipMatching(parent1, parent2)
        case parent2 => parent2
      }
    case _ => tp2
  }

  private def isSubRefinements(tp1: RefinedType, tp2: RefinedType, limit: Type): Boolean =
    isSubType(tp1.refinedInfo, tp2.refinedInfo)
    && ((tp2.parent eq limit)
       || isSubRefinements(
            tp1.parent.asInstanceOf[RefinedType],
            tp2.parent.asInstanceOf[RefinedType], limit))

  private def isCovered(tp: Type): Boolean = tp.dealiasKeepRefiningAnnots.stripTypeVar match {
    case tp: TypeRef => tp.symbol.isClass && tp.symbol != defn.NothingClass && tp.symbol != defn.NullClass
    case tp: AppliedType => isCovered(tp.tycon)
    case tp: RefinedOrRecType => isCovered(tp.parent)
    case tp: AndType => isCovered(tp.tp1) && isCovered(tp.tp2)
    case tp: OrType  => isCovered(tp.tp1) && isCovered(tp.tp2)
    case _ => false
  }

  private def narrowGADTBounds(tr: NamedType, bound: Type, approx: ApproxState, isUpper: Boolean): Boolean = {
    val tparam = tr.symbol
    !frozenConstraint && !frozenGadt
    && !approx.low && !approx.high
    && !bound.isRef(tparam)
    && ctx.gadtState.rollbackGadtUnless(ctx.gadtState.addBound(tparam, bound, isUpper))
  }

  private def matchingMethodParams(tp1: MethodType, tp2: MethodType, precise: Boolean = true): Boolean = {
    def loop(formals1: List[Type], formals2: List[Type]): Boolean = formals1 match {
      case formal1 :: rest1 =>
        formals2 match {
          case formal2 :: rest2 =>
            val formal2a = if (tp2.isParamDependent) formal2.subst(tp2, tp1) else formal2
            val paramsMatch =
              if precise then
                inFrozenConstraint(isSameType(formal1, formal2a))
              else if ctx.phase == Phases.checkCapturesPhase then
                // allow to constrain capture set variables
                isSubType(formal2a, formal1)
              else
                isSubTypeWhenFrozen(formal2a, formal1)
            paramsMatch && loop(rest1, rest2)
          case _ =>
            false
        }
      case _ =>
        formals2.isEmpty
    }
    val erasedValid = (!tp1.hasErasedParams && !tp2.hasErasedParams) || (tp1.erasedParams == tp2.erasedParams)

    erasedValid && loop(tp1.paramInfos, tp2.paramInfos)
  }

  private def matchingPolyParams(tp1: PolyType, tp2: PolyType): Boolean = {
    def loop(formals1: List[Type], formals2: List[Type]): Boolean = formals1 match {
      case formal1 :: rest1 =>
        formals2 match {
          case formal2 :: rest2 =>
            val formal2a = formal2.subst(tp2, tp1)
            isSubTypeWhenFrozen(formal2a, formal1) &&
            loop(rest1, rest2)
          case _ =>
            false
        }
      case _ =>
        formals2.isEmpty
    }
    loop(tp1.paramInfos, tp2.paramInfos)
  }

  private def isSameType(tp1: Type, tp2: Type): Boolean =
    if tp1 eq NoType then false
    else if tp1 eq tp2 then true
    else isSubType(tp1, tp2) && isSubType(tp2, tp1)

  private def subCaptures(refs1: CaptureSet, refs2: CaptureSet)(using Context) =
    refs1.subCaptures(refs2, frozenConstraint).isOK

  private def sameBoxed(tp1: Type, tp2: Type, refs1: CaptureSet)(using Context): Boolean =
    (tp1.isBoxedCapturing == tp2.isBoxedCapturing)
    || subCaptures(refs1, CaptureSet.empty)

  private def traceInfo(tp1: Type, tp2: Type) =
    i"$tp1 <:< tp2" + {
      if ctx.settings.verbose.value || Config.verboseExplainSubtype then
        s" ${tp1.className}, ${tp2.className}"
        + (if frozenConstraint then " frozen" else "")
      else ""
    }

  // ConstraintHandling
  private def subsumes(c1: Constraint, c2: Constraint, pre: Constraint)(using Context): Boolean =
    if      c2 eq pre then true
    else if c1 eq pre then false
    else
      val saved = constraint
      try pre.forallParams { p =>
        c1.entry(p).exists
          && c2.upper(p).forall(c1.isLess(p, _))
          && isSubTypeWhenFrozen(c1.nonParamBounds(p), c2.nonParamBounds(p))
      }
      finally constraint = saved

  private def canConstrain(param: TypeParamRef): Boolean = constraint.contains(param)
  private def addConstraint(param: TypeParamRef, bound: Type, fromBelow: Boolean): Boolean =
    if fromBelow
    then TypeComparer.necessarySubType(bound, param)
    else TypeComparer.necessarySubType(param, bound)

  private inline def subtyping = gadts
}
