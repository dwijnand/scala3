package dotty.tools.dotc
package transform
package patmat

import core._
import Types._
import Contexts._
import Flags._
import ast._
import Trees._
import Decorators._
import Symbols._
import StdNames._
import NameOps._
import Constants._
import typer._
import Applications._
import Inferencing._
import ProtoTypes._
import transform.SymUtils._
import reporting._
import config.Printers.{exhaustivity => debug}
import util.{SrcPos, NoSourcePosition}
import NullOpsDecorator._
import collection.mutable

/** Space logic for checking exhaustivity and unreachability of pattern matching
 *
 *  Space can be thought of as a set of possible values. A type or a pattern
 *  both refer to spaces. The space of a type is the values that inhabit the
 *  type. The space of a pattern is the values that can be covered by the
 *  pattern.
 *
 *  Space is recursively defined as follows:
 *
 *      1. `Empty` is a space
 *      2. For a type T, `Typ(T)` is a space
 *      3. A union of spaces `S1 | S2 | ...` is a space
 *      4. `Prod(S1, S2, ..., Sn)` is a product space.
 *
 *  For the problem of exhaustivity check, its formulation in terms of space is as follows:
 *
 *      Is the space Typ(T) a subspace of the union of space covered by all the patterns?
 *
 *  The problem of unreachable patterns can be formulated as follows:
 *
 *      Is the space covered by a pattern a subspace of the space covered by previous patterns?
 *
 *  Assumption:
 *    (1) One case class cannot be inherited directly or indirectly by another
 *        case class.
 *    (2) Inheritance of a case class cannot be well handled by the algorithm.
 *
 */

/** space definition */
sealed trait Space

/** Empty space */
case object Empty extends Space

/** Space representing the set of all values of a type
 *
 * @param tp: the type this space represents
 * @param decomposed: does the space result from decomposition? Used for pretty print
 *
 */
case class Typ(tp: Type, decomposed: Boolean = true) extends Space

/** Space representing an extractor pattern */
case class Prod(tp: Type, unappTp: TermRef, params: List[Space]) extends Space

/** Union of spaces */
case class Or(spaces: Seq[Space]) extends Space

/** abstract space logic */
trait SpaceLogic {
  /** Is `tp1` a subtype of `tp2`? */
  def isSubType(tp1: Type, tp2: Type): Boolean

  /** True if we can assume that the two unapply methods are the same.
   *  That is, given the same parameter, they return the same result.
   *
   *  We assume that unapply methods are pure, but the same method may
   *  be called with different prefixes, thus behaving differently.
   */
  def isSameUnapply(tp1: TermRef, tp2: TermRef): Boolean

  /** Return a space containing the values of both types.
   *
   * The types should be atomic (non-decomposable) and unrelated (neither
   * should be a subtype of the other).
   */
  def intersectUnrelatedAtomicTypes(tp1: Type, tp2: Type): Space

  /** Is the type `tp` decomposable? i.e. all values of the type can be covered
   *  by its decomposed types.
   *
   * Abstract sealed class, OrType, Boolean and Java enums can be decomposed.
   */
  def canDecompose(tp: Type): Boolean

  /** Return term parameter types of the extractor `unapp` */
  def signature(unapp: TermRef, scrutineeTp: Type, argLen: Int): List[Type]

  /** Get components of decomposable types */
  def decompose(tp: Type): List[Typ]

  /** Whether the extractor covers the given type */
  def covers(unapp: TermRef, scrutineeTp: Type, argLen: Int): Boolean

  /** Display space in string format */
  def show(sp: Space): String

  /** Simplify space such that a space equal to `Empty` becomes `Empty` */
  def simplify(space: Space)(using Context): Space = trace(s"simplify ${show(space)} --> ", debug, show)(space match {
    case Prod(tp, fun, spaces) =>
      val sps = spaces.map(simplify(_))
      if (sps.contains(Empty)) Empty
      else if (canDecompose(tp) && decompose(tp).isEmpty) Empty
      else Prod(tp, fun, sps)
    case Or(spaces) =>
      val spaces2 = spaces.map(simplify(_)).filter(_ != Empty)
      if spaces2.isEmpty then Empty
      else if spaces2.lengthCompare(1) == 0 then spaces2.head
      else Or(spaces2)
    case Typ(tp, _) =>
      if (canDecompose(tp) && decompose(tp).isEmpty) Empty
      else space
    case _ => space
  })

  /** Remove a space if it's a subspace of remaining spaces
   *
   *  Note: `dedup` will return the same result if the sequence >= 10
   */
  def dedup(spaces: Seq[Space])(using Context): Seq[Space] =
    if (spaces.lengthCompare(1) <= 0 || spaces.lengthCompare(10) >= 0) spaces
    else {
      val res = spaces.map(sp => (sp, spaces.filter(_ ne sp))).find {
        case (sp, sps) => isSubspace(sp, Or(LazyList(sps: _*)))
      }
      if (res.isEmpty) spaces
      else res.get._2
    }

  /** Flatten space to get rid of `Or` for pretty print */
  def flatten(space: Space)(using Context): Seq[Space] = space match {
    case Prod(tp, fun, spaces) =>
      val ss = LazyList(spaces: _*).map(flatten)

      ss.foldLeft(LazyList(Nil : List[Space])) { (acc, flat) =>
        for { sps <- acc; s <- flat }
        yield sps :+ s
      }.map { sps =>
        Prod(tp, fun, sps)
      }

    case Or(spaces) =>
      LazyList(spaces: _*).flatMap(flatten)

    case _ =>
      List(space)
  }

  private def mkProd1(tp: Type, prod: Prod) =
    Prod(tp, prod.unappTp, signature(prod.unappTp, tp, prod.params.length).map(Typ(_, false)))

  private def isSimplyEmpty(s: Space)(using Context) = simplify(s) == Empty

  /** Is `a` a subspace of `b`? Equivalent to `a - b == Empty`, but faster */
  def isSubspace(a: Space, b: Space)(using Context): Boolean = trace(s"isSubspace(${show(a)}, ${show(b)})", debug) {
    def tryDecompose1(tp: Type) = canDecompose(tp) && isSubspace(Or(decompose(tp)), b)
    def tryDecompose2(tp: Type) = canDecompose(tp) && isSubspace(a, Or(decompose(tp)))

    (simplify(a), simplify(b)) match {
      case (Empty, _)                               => true
      case (_, Empty)                               => false
      case (Typ(tp1, _), Typ(tp2, _))               => isSubType(tp1, tp2) || tryDecompose1(tp1) || tryDecompose2(tp2)
      case (Typ(tp1, _), Or(ss))                    => ss.exists(isSubspace(a, _)) || tryDecompose1(tp1) // optimization: don't go to subtraction too early
      case (Or(ss), _)                              => ss.forall(isSubspace(_, b))
      case (_, Or(_))                               => isSimplyEmpty(minus(a, b))
      case (Prod(tp1, _, _), Typ(tp2, _))           => isSubType(tp1, tp2)
      case (Typ(tp1, _), prod @ Prod(tp2, fun, ss)) => isSubType(tp1, tp2) && covers(fun, tp1, ss.length) && isSubspace(mkProd1(tp2, prod), b)
      case (Prod(_, fun1, ss1), Prod(_, fun2, ss2)) => isSameUnapply(fun1, fun2) && ss1.zip(ss2).forall((isSubspace _).tupled)
    }
  }

  /** Intersection of two spaces */
  def intersect(a: Space, b: Space)(using Context): Space = trace(s"${show(a)} & ${show(b)}", debug, show) {
    def tryDecompose1(tp: Type) = intersect(Or(decompose(tp)), b)
    def tryDecompose2(tp: Type) = intersect(a, Or(decompose(tp)))

    (a, b) match {
      case (Empty, _) | (_, Empty)                           => Empty

      case (_, Or(ss))                                       => Or(ss.map(intersect(a, _)).filter(_ ne Empty))
      case (Or(ss), _)                                       => Or(ss.map(intersect(_, b)).filter(_ ne Empty))

      case (Typ(tp1, _), Typ(tp2, _)) if isSubType(tp1, tp2) => a
      case (Typ(tp1, _), Typ(tp2, _)) if isSubType(tp2, tp1) => b
      case (Typ(tp1, _), Typ(tp2, _)) if canDecompose(tp1)   => tryDecompose1(tp1)
      case (Typ(tp1, _), Typ(tp2, _)) if canDecompose(tp2)   => tryDecompose2(tp2)
      case (Typ(tp1, _), Typ(tp2, _))                        => intersectUnrelatedAtomicTypes(tp1, tp2)

      case (Typ(tp1, _), Prod(tp2, fun, ss)) if isSubType(tp2, tp1) => b
      case (Typ(tp1, _), Prod(tp2, fun, ss)) if canDecompose(tp1)   => tryDecompose1(tp1)
      case (Typ(tp1, _), Prod(tp2, fun, ss)) if isSubType(tp1, tp2) => a // problematic corner case: inheriting a case class
      case (Typ(tp1, _), Prod(tp2, fun, ss))                        => intersectUnrelatedAtomicTypes(tp1, tp2)

      case (Prod(tp1, fun, ss), Typ(tp2, _)) if isSubType(tp1, tp2) => a
      case (Prod(tp1, fun, ss), Typ(tp2, _)) if canDecompose(tp2)   => tryDecompose2(tp2)
      case (Prod(tp1, fun, ss), Typ(tp2, _)) if isSubType(tp2, tp1) => b // problematic corner case: inheriting a case class
      case (Prod(tp1, fun, ss), Typ(tp2, _))                        => intersectUnrelatedAtomicTypes(tp1, tp2)

      case (Prod(tp1, fun1, ss1), Prod(tp2, fun2, ss2)) if !isSameUnapply(fun1, fun2)                                     => intersectUnrelatedAtomicTypes(tp1, tp2)
      case (Prod(tp1, fun1, ss1), Prod(tp2, fun2, ss2)) if fun1.symbol.name == nme.unapply && ss1.length != ss2.length    => intersectUnrelatedAtomicTypes(tp1, tp2)
      case (Prod(tp1, fun1, ss1), Prod(tp2, fun2, ss2)) if ss1.zip(ss2).exists(p => isSimplyEmpty(intersect(p._1, p._2))) => Empty
      case (Prod(tp1, fun1, ss1), Prod(tp2, fun2, ss2))                                                                   => Prod(tp1, fun1, ss1.zip(ss2).map((intersect _).tupled))
    }
  }

  /** The space of a not covered by b */
  def minus(a: Space, b: Space)(using Context): Space = trace.force(s"${show(a)} - ${show(b)}", debug, show) { (a, b) match {
    case (Empty, _)  => Empty
    case (_, Empty)  => a
    case (Or(ss), _) => Or(ss.map(minus(_, b)))
    case (_, Or(ss)) => ss.foldLeft(a)(minus)

    case ( Typ(tp1, _),    Typ(tp2, _))       if isSubType(tp1, tp2)                                => Empty
    case ( Typ(tp1, _), p@Prod(tp2, fun, ss)) if isSubType(tp1, tp2) && covers(fun, tp1, ss.length) => minus(mkProd1(tp1, p), b) // rationale: every instance of `tp1` is covered by `tp2(_)`
    case (Prod(tp1, _, _), Typ(tp2, _))       if isSubType(tp1, tp2)                                => Empty // uncovered corner case: tp2 :< tp1, may happen when inheriting case class
    case (Prod(tp1, _, _), Typ(tp2, _))       if isSimplyEmpty(a)                                   => Empty

    case ( Typ(tp1, _),    Typ(tp2, _))    if canDecompose(tp1) => minus(Or(decompose(tp1)), b)
    case ( Typ(tp1, _),    Typ(tp2, _))    if canDecompose(tp2) => minus(a, Or(decompose(tp2)))
    case ( Typ(tp1, _),   Prod(tp2, _, _)) if canDecompose(tp1) => minus(Or(decompose(tp1)), b)
    case (Prod(tp1, _, _), Typ(tp2, _))    if canDecompose(tp2) => minus(a, Or(decompose(tp2)))

    case (Typ(_, _), Typ(_, _))     => a
    case (Typ(_, _), Prod(_, _, _)) => a
    case (Prod(_, _, _), Typ(_, _)) => a

    case (Prod(tp1, fun1, ss1), Prod(tp2, fun2, ss2)) if !isSameUnapply(fun1, fun2) => a
    case (Prod(tp1, fun1, ss1), Prod(tp2, fun2, ss2)) =>
      val range = (0 until ss1.size).toList
      val cache = Array.fill[Space](ss2.length)(null)
      def sub(i: Int) = { if cache(i) == null then cache(i) = minus(ss1(i), ss2(i)); cache(i) }
           if range.exists(i => isSubspace(ss1(i), sub(i))) then a
      else if cache.forall(sub => isSubspace(sub, Empty))   then Empty
      else
        // `(_, _, _) - (Some, None, _)` becomes `(None, _, _) | (_, Some, _) | (_, _, Empty)`
        Or(LazyList(range: _*).flatMap { i =>
          flatten(sub(i)).map(s => Prod(tp1, fun1, ss1.updated(i, s)))
        })
  }}
}

object SpaceEngine {

  /** Is the unapply or unapplySeq irrefutable?
   *  @param  unapp   The unapply function reference
   */
  def isIrrefutable(unapp: TermRef, argLen: Int)(using Context): Boolean = {
    val unappResult = unapp.widen.finalResultType
    unappResult.isRef(defn.SomeClass)
    || unappResult <:< ConstantType(Constant(true)) // only for unapply
    || (unapp.symbol.is(Synthetic) && unapp.symbol.owner.linkedClass.is(Case))  // scala2 compatibility
    || unapplySeqTypeElemTp(unappResult).exists // only for unapplySeq
    || isProductMatch(unappResult, argLen)
    || {
      val isEmptyTp = extractorMemberType(unappResult, nme.isEmpty, NoSourcePosition)
      isEmptyTp <:< ConstantType(Constant(false))
    }
  }

  /** Is the unapply or unapplySeq irrefutable?
   *  @param  unapp   The unapply function tree
   */
  def isIrrefutable(unapp: tpd.Tree, argLen: Int)(using Context): Boolean = {
    val fun1 = tpd.funPart(unapp)
    val funRef = fun1.tpe.asInstanceOf[TermRef]
    isIrrefutable(funRef, argLen)
  }
}

/** Scala implementation of space logic */
class SpaceEngine(using Context) extends SpaceLogic {
  import tpd._, SpaceEngine._

  private val scalaSeqFactoryClass = defn.SeqFactoryClass
  private val scalaListType        = defn.ListClass.typeRef
  private val  scalaNilType        = defn.NilModule.termRef
  private val scalaConsType        = defn.ConsClass.typeRef

  private val constantNullType     = ConstantType(Constant(null))

  /** Does the given tree stand for the literal `null`? */
  def isNullLit(tree: Tree): Boolean = tree match {
    case Literal(Constant(null)) => true
    case _                       => false
  }

  override def intersectUnrelatedAtomicTypes(tp1: Type, tp2: Type): Space = trace(s"atomic intersection: ${AndType(tp1, tp2).show}", debug) {
    // Precondition: !isSubType(tp1, tp2) && !isSubType(tp2, tp1).
    if !ctx.explicitNulls && (tp1.isNullType || tp2.isNullType) then Empty // Since projections of types don't include null, intersection with null is empty.
    else if TypeComparer.provablyDisjoint(tp1, tp2) then Empty
    else Typ(AndType(tp1, tp2), decomposed = true)
  }

  /** Return the space that represents the pattern `pat` */
  def project(pat: Tree): Space = pat match {
    case Literal(Constant(s: Symbol))    => Typ(s.termRef,       decomposed = false)
    case Literal(c)                      => Typ(ConstantType(c), decomposed = false)
    case pat: Ident if isBackquoted(pat) => Typ(pat.tpe, decomposed = false)
    case Ident(_) | Select(_, _)         => Typ(erase(pat.tpe.stripAnnots.widenSkolem, isValue = true), decomposed = false)
    case Alternative(trees)              => Or(trees.map(project))
    case Bind(_, pat)                    => project(pat)
    case SeqLiteral(pats, _)             => projectSeq(pats)

    case UnApply(fun, _, pats) =>
      val funRef = funPart(fun).tpe.asInstanceOf[TermRef]
      if fun.symbol.name == nme.unapplySeq then
        if fun.symbol.owner == scalaSeqFactoryClass then projectSeq(pats)
        else
          val (arity, elemTp, resultTp) = unapplySeqInfo(fun.tpe.widen.finalResultType, fun.srcPos)
          val params1 = if elemTp.exists then List(projectSeq(pats))
            else pats.take(arity - 1).map(project) :+ projectSeq(pats.drop(arity - 1))
          Prod(erase(pat.tpe.stripAnnots, isValue = false), funRef, params1)
      else
        Prod(erase(pat.tpe.stripAnnots, isValue = false), funRef, pats.map(project))

    case Typed(pat @ UnApply(_, _, _), _) => project(pat)
    case Typed(_, tpt)                    => Typ(erase(tpt.tpe.stripAnnots, isValue = true), decomposed = false)
    case This(_)                          => Typ(pat.tpe.stripAnnots, decomposed = false)
    case EmptyTree                        => Typ(WildcardType, decomposed = false) // default rethrow clause of try/catch, check tests/patmat/try2.scala
    case Block(Nil, expr)                 => project(expr)
    case _                                => Typ(pat.tpe.narrow, decomposed = false) // Pattern is an arbitrary expression; assume a skolem (i.e. an unknown value) of the pattern type
  }

  private def project(tp: Type): Space = tp match {
    case OrType(tp1, tp2) => Or(List(project(tp1), project(tp2)))
    case tp               => Typ(tp, decomposed = true)
  }

  private def unapplySeqInfo(resTp: Type, pos: SrcPos)(using Context): (Int, Type, Type) = {
    var resultTp = resTp
    var elemTp   = unapplySeqTypeElemTp(resultTp)
    var arity    = productArity(resultTp, pos)
    if !elemTp.exists && arity <= 0 then
      resultTp = resTp.select(nme.get).finalResultType
      elemTp = unapplySeqTypeElemTp(resultTp.widen)
      arity = productSelectorTypes(resultTp, pos).size
    (arity, elemTp, resultTp)
  }

  /** Erase pattern bound types with WildcardType
   *
   *  For example, the type `C[T$1]` should match any `C[?]`, thus
   *  `v` should be `WildcardType` instead of `T$1`:
   *
   *     sealed trait B
   *     case class C[T](v: T) extends B
   *     (b: B) match {
   *        case C(v) =>      //    case C.unapply[T$1 @ T$1](v @ _):C[T$1]
   *     }
   *
   *  However, we cannot use WildcardType for Array[?], due to that
   *  `Array[WildcardType] <: Array[Array[WildcardType]]`, which may
   *  cause false unreachable warnings. See tests/patmat/t2425.scala
   *
   *  We cannot use type erasure here, as it would lose the constraints
   *  involving GADTs. For example, in the following code, type
   *  erasure would loose the constraint that `x` and `y` must be
   *  the same type, resulting in false inexhaustive warnings:
   *
   *     sealed trait Expr[T]
   *     case class IntExpr(x: Int) extends Expr[Int]
   *     case class BooleanExpr(b: Boolean) extends Expr[Boolean]
   *
   *     def foo[T](x: Expr[T], y: Expr[T]) = (x, y) match {
   *       case (IntExpr(_), IntExpr(_)) =>
   *       case (BooleanExpr(_), BooleanExpr(_)) =>
   *     }
   *
   *  @param inArray whether `tp` is a type argument to `Array`
   *  @param isValue whether `tp` is the type which match against values
   *
   *  If `isValue` is true, then pattern-bound symbols are erased to its upper bound.
   *  This is needed to avoid spurious unreachable warnings. See tests/patmat/i6197.scala.
   */
  private def erase(tp: Type, inArray: Boolean = false, isValue: Boolean = false): Type = trace(i"$tp erased to", debug)(tp match {
    case tp @ AppliedType(tycon, args) if tycon.typeSymbol.isPatternBound => WildcardType
    case tp @ AppliedType(tycon, args)                                    => tp.derivedAppliedType(erase(tycon, inArray, isValue = false), args.map(erase(_, inArray = tycon.isRef(defn.ArrayClass), isValue = false)))
    case tp @ OrType(tp1, tp2)                                            =>  OrType(erase(tp1, inArray, isValue), erase(tp2, inArray, isValue), tp.isSoft)
    case AndType(tp1, tp2)                                                => AndType(erase(tp1, inArray, isValue), erase(tp2, inArray, isValue))
    case tp @ RefinedType(parent, _, _)                                   => erase(parent, inArray, isValue)
    case tp: TypeRef if tp.symbol.isPatternBound && inArray               => tp.underlying
    case tp: TypeRef if tp.symbol.isPatternBound && isValue               => tp.superType
    case tp: TypeRef if tp.symbol.isPatternBound                          => WildcardType
    case _                                                                => tp
  })

  /** Space of the pattern: unapplySeq(a, b, c: _*) */
  def projectSeq(pats: List[Tree]): Space = {
    val tpe = pats match {
      case pat1 :: _ => pat1.tpe.widen
      case _         => return Typ(scalaNilType, false)
    }

    val unapplyTp = scalaConsType.classSymbol.companionModule.termRef.select(nme.unapply)

    val (items, zero) = pats match {
      case init :+ last if isWildcardStarArg(last) =>
        (init, Typ(scalaListType.appliedTo(last.tpe.elemType), false))
      case _ =>
        (pats, Typ(scalaNilType, false))
    }

    items.foldRight[Space](zero) { (pat, acc) =>
      Prod(scalaConsType.appliedTo(tpe), unapplyTp, List(project(pat), acc))
    }
  }

  /** Numeric literals, while being constant values of unrelated types (e.g. Char and Int),
   *  when used in a case may end up matching at runtime, because their equals may returns true.
   *  Because these are universally available, general purpose types, it would be good to avoid
   *  returning false positive warnings, such as in `(c: Char) match { case 67 => ... }` emitting a
   *  reachability warning on the case.  So the type `ConstantType(Constant(67, IntTag))` is
   *  converted to `ConstantType(Constant(67, CharTag))`.  #12805 */
  def convertConstantType(tp: Type, pt: Type): Type = tp match
    case tp @ ConstantType(const) =>
      val converted = const.convertTo(pt)
      if converted == null then tp else ConstantType(converted)
    case _ => tp

  def isPrimToBox(tp: Type, pt: Type) =
    tp.classSymbol.isPrimitiveValueClass && (defn.boxedType(tp).classSymbol eq pt.classSymbol)

  /** Adapt types by performing primitive value unboxing or boxing, or numeric constant conversion.  #12805
   *
   *  This makes these isSubType cases work like this:
   *  {{{
   *   1      <:< Integer  => (<skolem> : Integer) <:< Integer  = true
   *  ONE     <:< Int      => (<skolem> : Int)     <:< Int      = true
   *  Integer <:< (1: Int) => (<skolem> : Int)     <:< (1: Int) = false
   *  }}}
   */
  def adaptType(tp1: Type, tp2: Type): Type = trace(i"adaptType($tp1, $tp2)", show = true) {
    if      isPrimToBox(tp1, tp2) then defn.boxedType(tp1).narrow
    else if isPrimToBox(tp2, tp1) then defn.unboxedType(tp1).narrow
    else convertConstantType(tp1, tp2)
  }

  private val isSubspaceCache = mutable.HashMap.empty[(Space, Space, Context), Boolean]

  override def isSubspace(a: Space, b: Space)(using Context): Boolean =
    isSubspaceCache.getOrElseUpdate((a, b, ctx), super.isSubspace(a, b))

  private var isSubTypeCache = scala.collection.mutable.Map.empty[(Type, Type), Boolean]

  /** Is `tp1` a subtype of `tp2`?  */
  def isSubType(tp1: Type, tp2: Type): Boolean = isSubTypeCache.getOrElseUpdate((tp1, tp2), {
    //debug.println(TypeComparer.explained(_.isSubType(tp1, tp2)))
    isSubTypeImpl(tp1, tp2)
  })

  private def isSubTypeImpl(tp1: Type, tp2: Type): Boolean = trace(i"$tp1 <:< $tp2", debug, show = true) {
    (ctx.explicitNulls || tp1 != constantNullType || tp2 == constantNullType) && {
      val tp3 = adaptType(tp1)
      val res = tp3 <:< tp2
      debug.println(s"isSubType: ${tp3.show} <:< ${tp2.show} = $res")
      res
    }
  }

  def isSameUnapply(tp1: TermRef, tp2: TermRef): Boolean =
    // always assume two TypeTest[S, T].unapply are the same if they are equal in types
    (tp1.prefix.isStable && tp2.prefix.isStable || tp1.symbol == defn.TypeTest_unapply)
    && tp1 =:= tp2

  /** Parameter types of the case class type `tp`. Adapted from `unapplyPlan` in patternMatcher  */
  def signature(unapp: TermRef, scrutineeTp: Type, argLen: Int): List[Type] = {
    val unappSym = unapp.symbol

    // println("scrutineeTp = " + scrutineeTp.show)

    val mt: MethodType = unapp.widen match {
      case mt: MethodType => mt
      case pt: PolyType   =>
        inContext(ctx.fresh.setExploreTyperState()) {
          val tvars = pt.paramInfos.map(newTypeVar(_))
          val mt = pt.instantiate(tvars).asInstanceOf[MethodType]
          scrutineeTp <:< mt.paramInfos(0)
          // force type inference to infer a narrower type: could be singleton
          // see tests/patmat/i4227.scala
          mt.paramInfos(0) <:< scrutineeTp
          isFullyDefined(mt, ForceDegree.all)
          mt
        }
    }

    // Case unapply:
    // 1. return types of constructor fields if the extractor is synthesized for Scala2 case classes & length match
    // 2. return Nil if unapply returns Boolean  (boolean pattern)
    // 3. return product selector types if unapply returns a product type (product pattern)
    // 4. return product selectors of `T` where `def get: T` is a member of the return type of unapply & length match (named-based pattern)
    // 5. otherwise, return `T` where `def get: T` is a member of the return type of unapply
    //
    // Case unapplySeq:
    // 1. return the type `List[T]` where `T` is the element type of the unapplySeq return type `Seq[T]`

    val resTp = mt.instantiate(scrutineeTp :: Nil).finalResultType

    val sig =
      if (resTp.isRef(defn.BooleanClass))
        List()
      else {
        val isUnapplySeq = unappSym.name == nme.unapplySeq

        if (isUnapplySeq) {
          val (arity, elemTp, resultTp) = unapplySeqInfo(resTp, unappSym.srcPos)
          if (elemTp.exists) scalaListType.appliedTo(elemTp) :: Nil
          else {
            val sels = productSeqSelectors(resultTp, arity, unappSym.srcPos)
            sels.init :+ scalaListType.appliedTo(sels.last)
          }
        }
        else {
          val arity = productArity(resTp, unappSym.srcPos)
          if (arity > 0)
            productSelectorTypes(resTp, unappSym.srcPos)
          else {
            val getTp = resTp.select(nme.get).finalResultType.widenTermRefExpr
            if (argLen == 1) getTp :: Nil
            else productSelectorTypes(getTp, unappSym.srcPos)
          }
        }
      }

    debug.println(s"signature of ${unappSym.showFullName} ----> ${sig.map(_.show).mkString("[", ", ", "]")}")

    sig.map(_.annotatedToRepeated)
  }

  /** Whether the extractor covers the given type */
  def covers(unapp: TermRef, scrutineeTp: Type, argLen: Int): Boolean =
    SpaceEngine.isIrrefutable(unapp, argLen) || unapp.symbol == defn.TypeTest_unapply && {
      val AppliedType(_, _ :: tp :: Nil) = unapp.prefix.widen.dealias
      scrutineeTp <:< tp
    }

  /** Decompose a type into subspaces -- assume the type can be decomposed */
  def decompose(tp: Type): List[Typ] = tp.dealias match {
    case AndType(tp1, tp2) =>
      def decomposeComponent(tpA: Type, tpB: Type): List[Typ] =
        decompose(tpA).flatMap { case Typ(tp, _) =>
               if tp <:< tpB then List(Typ(tp,  decomposed = true))
          else if tpB <:< tp then List(Typ(tpB, decomposed = true))
          else if TypeComparer.provablyDisjoint(tp, tpB) then Nil
          else List(Typ(AndType(tp, tpB), decomposed = true))
        }
      if canDecompose(tp1) then decomposeComponent(tp1, tp2) else decomposeComponent(tp2, tp1)

    case OrType(tp1, tp2) => List(Typ(tp1, true), Typ(tp2, true))

    case tp if tp.isRef(defn.BooleanClass) => List(
      Typ(ConstantType(Constant(true)), true),
      Typ(ConstantType(Constant(false)), true)
    )

    case tp if tp.isRef(defn.UnitClass) =>
      List(Typ(ConstantType(Constant(())), true))

    case tp if tp.classSymbol.isAllOf(JavaEnumTrait) =>
      tp.classSymbol.children.map(sym => Typ(sym.termRef, true))

    case tp =>
      val children = tp.classSymbol.children
      debug.println(s"decompose: ${tp.show} =>? [${children.map(_.show).mkString(", ")}]")

      val parts = children.map { sym =>
        val sym1    = if sym.is(ModuleClass) then sym.sourceModule else sym
        val refined = TypeOps.refineUsingParent(tp, sym1)

        debug.println(s"decompose: ${sym1.show} refined to ${refined.show}")

        def inhabited(tp: Type): Boolean = tp.dealias match {
          case AndType(tp1, tp2) => !TypeComparer.provablyDisjoint(tp1, tp2)
          case  OrType(tp1, tp2) => inhabited(tp1) || inhabited(tp2)
          case tp: RefinedType   => inhabited(tp.parent)
          case tp: TypeRef       => inhabited(tp.prefix)
          case _                 => true
        }

        if inhabited(refined) then refined else NoType
      }.filter(_.exists)

      debug.println(s"decompose: ${tp.show} =>  [${parts.map(_.show).mkString(", ")}]")
      parts.map(Typ(_, true))
  }

  private var canDecomposeCache = scala.collection.mutable.Map.empty[Type, Boolean]

  /** Abstract sealed types, or-types, Boolean and Java enums can be decomposed */
  def canDecompose(tp: Type): Boolean = canDecomposeCache.getOrElseUpdate(tp, {
    val res = tp.dealias match
      case _: SingletonType  => false
      case OrType(_, _)      => true
      case AndType(tp1, tp2) => canDecompose(tp1) || canDecompose(tp2)
      case _                 =>
        val cls = tp.classSymbol
        cls.is(Sealed) && cls.isOneOf(AbstractOrTrait) && cls.children.nonEmpty && !cls.hasAnonymousChild
        || cls.isAllOf(JavaEnumTrait) || tp.isRef(defn.BooleanClass) || tp.isRef(defn.UnitClass)
    debug.println(s"decomposable: ${tp.show} = $res")
    res
  })

  /** Show friendly type name with current scope in mind
   *
   *  E.g.    C.this.B     -->  B     if current owner is C
   *          C.this.x.T   -->  x.T   if current owner is C
   *          X[T]         -->  X
   *          C            -->  C     if current owner is C !!!
   */
  def showType(tp: Type, showTypeArgs: Boolean = false): String = {
    val enclosingCls = ctx.owner.enclosingClass

    def isOmittable(sym: Symbol) =
      sym.isEffectiveRoot                                           ||
      sym.isAnonymousClass                                          ||
      sym.name.isReplWrapperName                                    ||
      ctx.definitions.unqualifiedOwnerTypes.exists(_.symbol == sym) ||
      sym.showFullName.startsWith("scala.")                         ||
      sym == enclosingCls                                           ||
      sym == enclosingCls.sourceModule

    def refinePrefix(tp: Type): String = tp match {
      case NoPrefix                                => ""
      case tp: NamedType if isOmittable(tp.symbol) => ""
      case tp: ThisType                            => refinePrefix(tp.tref)
      case tp: RefinedType                         => refinePrefix(tp.parent)
      case tp: NamedType                           => tp.name.show.stripSuffix("$")
      case tp: TypeVar                             => refinePrefix(tp.instanceOpt)
      case _                                       => tp.show
    }

    def refine(tp: Type): String = tp.stripped match {
      case tp: RefinedType => refine(tp.parent)
      case tp: AppliedType => refine(tp.typeConstructor) + (if showTypeArgs then tp.argInfos.map(refine).mkString("[", ",", "]") else "")
      case tp: ThisType    => refine(tp.tref)
      case tp: NamedType   =>
        val pre = refinePrefix(tp.prefix)
             if tp.name == tpnme.higherKinds then pre
        else if pre.isEmpty                  then tp.name.show.stripSuffix("$")
        else                                      s"$pre.${tp.name.show.stripSuffix("$")}"
      case tp: OrType    => refine(tp.tp1) + " | " + refine(tp.tp2)
      case _: TypeBounds => "_"
      case _             => tp.show.stripSuffix("$")
    }

    refine(tp)
  }

  /** Whether the counterexample is satisfiable. The space is flattened and non-empty. */
  def satisfiable(sp: Space): Boolean = {
    def impossible = throw new AssertionError("`satisfiable` only accepts flattened space.")

    def genConstraint(space: Space): List[(Type, Type)] = space match {
      case Prod(tp, unappTp, ss) => ss.zip(signature(unappTp, tp, ss.length)).flatMap {
        case (sp: Prod, tp)     => sp.tp -> tp :: genConstraint(sp)
        case (Typ(tp1, _), tp2) => List(tp1 -> tp2)
        case _                  => impossible
      }
      case Typ(_, _) => Nil
      case _         => impossible
    }

    def checkConstraint(constrs: List[(Type, Type)])(using Context): Boolean = {
      val tvarMap = collection.mutable.Map.empty[Symbol, TypeVar]
      val typeParamMap = new TypeMap() {
        override def apply(tp: Type): Type = tp match {
          case tref: TypeRef if tref.symbol.is(TypeParam) =>
            tvarMap.getOrElseUpdate(tref.symbol, newTypeVar(tref.underlying.bounds))
          case tp => mapOver(tp)
        }
      }

      constrs.forall { case (tp1, tp2) => typeParamMap(tp1) <:< typeParamMap(tp2) }
    }

    checkConstraint(genConstraint(sp))(using ctx.fresh.setNewTyperState())
  }

  /** Display spaces */
  def show(ss: Seq[Space]): String = ss.map(show).mkString(", ")
  def show(s: Space): String = {
    def params(tp: Type): List[Type] = tp.classSymbol.primaryConstructor.info.firstParamTypes

    /** does the companion object of the given symbol have custom unapply */
    def hasCustomUnapply(sym: Symbol): Boolean = {
      def has(name: Names.Name) =
        sym.companionModule.findMember(name, NoPrefix, required = EmptyFlags, excluded = Synthetic).exists
      has(nme.unapply) || has(nme.unapplySeq)
    }

    def ppXs(ss: Seq[Space]): String = ss.map(pp).mkString("[", ", ", "]")
    def pp(s: Space): String         = s match
      case Empty                 => "Empty"
      case Typ(tp, _)            => s"Typ(${tp.show})"
      case Prod(tp, fun, params) => s"Prod(${tp.show}, ${fun.show}, ${ppXs(params)})"
      case Or(ss)                => s"Or(${ppXs(ss)})"

    def doShow(s: Space, flattenList: Boolean = false): String = trace(s"space doShow(${pp(s)})", debug)(s match {
      case Empty                   => "empty"
      case Typ(c: ConstantType, _) => "" + c.value.value
      case Typ(tp: TermRef, _)     => if flattenList && tp <:< scalaNilType then "" else tp.symbol.showName
      case Typ(tp, decomposed)     =>
        val sym = tp.classSymbol
        if ctx.definitions.isTupleNType(tp) then params(tp).map(_ => "_").mkString("(", ", ", ")")
        else if scalaListType.isRef(sym) then if flattenList then "_*"    else "_: List"
        else if scalaConsType.isRef(sym) then if flattenList then "_, _*" else "List(_, _*)"
        else if tp.classSymbol.is(Sealed) && tp.classSymbol.hasAnonymousChild then s"_: ${showType(tp)} (anonymous)"
        else if tp.classSymbol.is(CaseClass) && !hasCustomUnapply(tp.classSymbol) then
          // use constructor syntax for case class
          showType(tp) + params(tp).map(_ => "_").mkString("(", ", ", ")")
        else
          val s = showType(tp, showTypeArgs = true)
          if decomposed then s"_: $s" else s"_{$s}"
      case Prod(tp, fun, params) =>
        if ctx.definitions.isTupleNType(tp) then params.map(doShow(_)).mkString("(", ", ", ")")
        else if tp.isRef(scalaConsType.symbol) then
          val ps = params.map(doShow(_, flattenList = true)).filter(_.nonEmpty)
          if flattenList then ps.mkString(", ") else ps.mkString("List(", ", ", ")")
        else
          val sym = fun.symbol
          val isUnapplySeq = sym.name.eq(nme.unapplySeq)
          val paramsStr = params.map(doShow(_, flattenList = isUnapplySeq)).mkString("(", ", ", ")")
          showType(fun.prefix) + paramsStr
      case Or(ss) => ss.map(doShow(_, flattenList)).mkString(" | ")
    })

    doShow(s, flattenList = false)
  }

  private def exhaustivityCheckable(sel: Tree): Boolean = {
    val seen = collection.mutable.Set.empty[Type]

    // Possible to check everything, but be compatible with scalac by default
    def isCheckable(tp: Type): Boolean =
      val tpw = tp.widen.dealias
      val classSym = tpw.classSymbol
      classSym.is(Sealed) ||
      tpw.isInstanceOf[OrType] ||
      (tpw.isInstanceOf[AndType] && {
        val and = tpw.asInstanceOf[AndType]
        isCheckable(and.tp1) || isCheckable(and.tp2)
      }) ||
      tpw.isRef(defn.BooleanClass) ||
      classSym.isAllOf(JavaEnumTrait) ||
      classSym.is(Case) && {
        if seen.add(tpw) then productSelectorTypes(tpw, sel.srcPos).exists(isCheckable(_))
        else true // recursive case class: return true and other members can still fail the check
      }

    val res = !sel.tpe.hasAnnotation(defn.UncheckedAnnot) && {
      ctx.settings.YcheckAllPatmat.value
      || isCheckable(sel.tpe)
    }

    debug.println(s"exhaustivity checkable: ${sel.show} = $res")
    res
  }

  /** Whether counter-examples should be further checked? True for GADTs. */
  private def shouldCheckExamples(tp: Type): Boolean =
    new TypeAccumulator[Boolean] {
      override def apply(b: Boolean, tp: Type): Boolean = tp match {
        case tref: TypeRef if tref.symbol.is(TypeParam) && variance != 1 => true
        case tp => b || foldOver(b, tp)
      }
    }.apply(false, tp)

  /** Return the underlying type of non-module, non-constant, non-enum case singleton types.
   *  Also widen ExprType to its result type, and rewrap any annotation wrappers.
   *  For example, with `val opt = None`, widen `opt.type` to `None.type`. */
  def toUnderlying(tp: Type)(using Context): Type = trace(i"toUnderlying($tp)", show = true)(tp match {
    case _: ConstantType                            => tp
    case tp: TermRef if tp.symbol.is(Module)        => tp
    case tp: TermRef if tp.symbol.isAllOf(EnumCase) => tp
    case tp: SingletonType                          => toUnderlying(tp.underlying)
    case tp: ExprType                               => toUnderlying(tp.resultType)
    case AnnotatedType(tp, annot)                   => AnnotatedType(toUnderlying(tp), annot)
    case _                                          => tp
  })

  def checkExhaustivity(_match: Match): Unit = {
    val Match(sel, cases) = _match
    debug.println(i"checking exhaustivity of ${_match}")

    if (!exhaustivityCheckable(sel)) return

    debug.println(s"exhaustivity: checking ${_match.show}")

    val selTyp = toUnderlying(sel.tpe).dealias
    debug.println(s"exhaustivity: selTyp = ${selTyp.show}")

    val     selSpace = project(selTyp)
    val patternSpace = Or(cases.foldLeft(List.empty[Space]) { case (spaces, CaseDef(pat, guard, _)) =>
      val space = if guard.isEmpty then project(pat) else Empty
      debug.println(s"exhaustivity: pat=${pat.show} ====> space=${show(space)}")
      space :: spaces
    })

    debug.println(s"exhaustivity:     selSpace = ${show(    selSpace)}")
    debug.println(s"exhaustivity: patternSpace = ${show(patternSpace)}")

    val space1 = minus(selSpace, patternSpace)
    debug.println(s"exhaustivity: space1 = ${show(space1)}")

    val space2 = simplify(space1)
    debug.println(s"exhaustivity: space2 = ${show(space2)}")

    val space3 = flatten(space2)
    debug.println(s"exhaustivity: space3 = ${show(space3)}")

    val checkGADTSAT = shouldCheckExamples(selTyp)
    val uncovered = space3.filter(s => s != Empty && (!checkGADTSAT || satisfiable(s)))
    debug.println(s"exhaustivity: uncovered = ${show(uncovered)}")

    if uncovered.nonEmpty then
      val hasMore = uncovered.lengthCompare(6) > 0
      val deduped = dedup(uncovered.take(6))
      val msg     = PatternMatchExhaustivity(show(deduped), hasMore)
      debug.println(s"uncovered=$msg")
      report.warning(msg, sel.srcPos)
  }

  private def redundancyCheckable(sel: Tree): Boolean =
    // Ignore Expr[T] and Type[T] for unreachability as a special case.
    // Quote patterns produce repeated calls to the same unapply method, but with different implicit parameters.
    // Since we assume that repeated calls to the same unapply method overlap
    // and implicit parameters cannot normally differ between two patterns in one `match`,
    // the easiest solution is just to ignore Expr[T] and Type[T].
    !sel.tpe.hasAnnotation(defn.UncheckedAnnot)
    && !sel.tpe.widen.isRef(defn.QuotedExprClass)
    && !sel.tpe.widen.isRef(defn.QuotedTypeClass)

  def checkRedundancy(_match: Match): Unit = {
    val Match(sel, _) = _match
    val cases = _match.cases.toIndexedSeq
    debug.println(i"checking redundancy in $_match")

    if (!redundancyCheckable(sel)) return

    val selTyp = toUnderlying(sel.tpe).dealias
    debug.println(i"selTyp = $selTyp")

    val isNullable = selTyp.classSymbol.isNullableClass
    val targetSpace = if isNullable
      then project(OrType(selTyp, constantNullType, soft = false))
      else project(selTyp)
    debug.println(s"targetSpace: ${show(targetSpace)}")

    var i        = 0
    val len      = cases.length
    var prevs    = List.empty[Space]
    var deferred = List.empty[Tree]

    while (i < len) {
      val CaseDef(pat, guard, _) = cases(i)

      debug.println(i"case pattern: $pat")

      val curr = project(pat)
      debug.println(i"reachable? ${show(curr)}")

      val prev = simplify(Or(prevs))
      debug.println(s"prev: ${show(prev)}")

      val covered = simplify(intersect(curr, targetSpace))
      debug.println(s"covered: ${show(covered)}")

      if prev == Empty && covered == Empty then // defer until a case is reachable
        deferred ::= pat
      else {
        for (pat <- deferred.reverseIterator)
          report.warning(MatchCaseUnreachable(), pat.srcPos)
        if pat != EmptyTree // rethrow case of catch uses EmptyTree
            && isSubspace(covered, prev)
        then {
          val nullOnly = isNullable && i == len - 1 && isWildcardArg(pat)
          val msg = if nullOnly then MatchCaseOnlyNullWarning() else MatchCaseUnreachable()
          report.warning(msg, pat.srcPos)
        }
        deferred = Nil
      }

      // in redundancy check, take guard as false in order to soundly approximate
      prevs ::= (if guard.isEmpty then covered else Empty)
      i += 1
    }
  }
}
