package dotty.tools.dotc
package typer

import dotty.tools.dotc.ast.{ Trees, tpd }
import core.*
import Types.*, Contexts.*, Flags.*, Symbols.*, Trees.*
import Decorators.*
import Variances.*
import NameKinds.*
import util.SrcPos
import config.Printers.variances
import config.Feature.migrateTo3
import reporting.trace
import printing.Formatting.hl

import scala.compiletime.uninitialized

/** Provides `check` method to check that all top-level definitions
 *  in tree are variance correct. Does not recurse inside methods.
 *  The method should be invoked once for each Template.
 */
object VarianceChecker {
  case class VarianceError(tvar: Symbol, required: Variance)
  def check(tree: tpd.Tree)(using Context): Unit =
    VarianceChecker().Traverser.traverse(tree)

  /** Check that variances of type lambda correspond to their occurrences in its body.
   *  Note: this is achieved by a mechanism separate from checking class type parameters.
   *  Question: Can the two mechanisms be combined in one?
   */
  def checkLambda(tree: tpd.LambdaTypeTree, bounds: TypeBounds)(using Context): Unit =
    def checkType(tpe: Type): Unit = tpe match
      case tl: HKTypeLambda if tl.isDeclaredVarianceLambda =>
        val checkOK = new TypeAccumulator[Boolean]:
          def error(p: TypeParamRef) =
            val paramName = p.paramName
            val v = p.lambdaParam.paramVarianceSign
            val v1 = p.lambdaParam.paramVariance
            val pos = tree.tparams.collectFirst {
              case tparam if tparam.name == paramName => tparam.srcPos
            }.getOrElse(tree.srcPos)
            report.error(em"${varianceLabel(v)} type parameter ${paramName.toTermName} occurs in ${varianceLabel(variance)} position in ${tl.resType}", pos)
            false
          def apply(x: Boolean, t: Type) = x && t.match
            case p: TypeParamRef if p.binder eq tl                                      => varianceConforms(variance, p.lambdaParam.paramVarianceSign) || error(p)
            case AnnotatedType(_, annot) if annot.symbol == defn.UncheckedVarianceAnnot => x
            case _                                                                      => foldOver(x, t)
        checkOK(true, tl.resType)
      case _ =>
    end checkType

    checkType(bounds.lo)
    checkType(bounds.hi)
  end checkLambda
}

class VarianceChecker(using Context) {
  import VarianceChecker.*
  import tpd.*

  private object Validator extends TypeAccumulator[Option[VarianceError]] {
    def vVarianceSign = if variance == 0 then "v=" else s"v${Variances.varianceSign(variance)}"

    private var base: Symbol = uninitialized

    /** The variance of a symbol occurrence of `tvar` seen at the level of the definition of `base`.
     *  The search proceeds from `base` to the owner of `tvar`.
     *  Initially the state is the accumulator's variance, but it might change along the search.
     */
    def relativeVariance(tvar: Symbol, base: Symbol, v: Variance): Variance =
    trace.force(i"relVar($tvar, $base${
      if base.is(Param) then " Param" else ""}${
      if base.isAllOf(PrivateLocal) then " PrivateLocal" else ""}${
      if base.isAliasType then " AliasType" else ""
    }, $v)${
      if base.maybeOwner.isTerm then " Term" else ""}${
      if base.maybeOwner.isAllOf(PrivateLocal) then " PrivateLocal" else ""}${
      if base.maybeOwner.is(Package) then " Package" else ""
    }"):
      if base == tvar.owner              then v
      else if isMethParam(base)          then relativeVariance(tvar, paramOuter(base), flip(v))
      else if base.owner.isTerm          then Bivariant
      else if base.owner.is(Package)     then Bivariant
      else if base.isAllOf(PrivateLocal) then Bivariant
      else if base.isAliasType           then relativeVariance(tvar, base.owner, Invariant)
      else                                    relativeVariance(tvar, base.owner, v)

    /** The next level to take into account when determining the
     *  relative variance with a method parameter as base. The method
     *  is always skipped. If the method is a constructor, we also skip
     *  its class owner, because constructors are not checked for variance
     *  relative to the type parameters of their own class. On the other
     *  hand constructors do count for checking the variance of type parameters
     *  of enclosing classes. I believe the Scala 2 rules are too lenient in
     *  that respect.
     */
    private def paramOuter(param: Symbol) =
      val meth = param.owner
      if meth.isConstructor then meth.owner.owner else meth.owner

    private def isMethParam(sym: Symbol) =
      sym.is(Param) && sym.owner.isTerm && !sym.owner.isAllOf(PrivateLocal)

    /** Check variance of abstract type `tvar` when referred from `base`. */
    private def checkVarianceOfSymbol(tvar: Symbol): Option[VarianceError] =
    trace.force(i"checkVarianceOfSymbol($tvar) $vVarianceSign") {
      val required = relativeVariance(tvar, base, varianceFromInt(variance))
      if tvar.isOneOf(required)
      then None
      else Some(VarianceError(tvar, required))
      //else Option.empty[VarianceError]
    }

    /** For PolyTypes, type parameters are skipped because they are defined
     *  explicitly (their TypeDefs will be passed here.) For MethodTypes, the
     *  same is true of the parameters (ValDefs).
     */
    def apply(status: Option[VarianceError], tp: Type): Option[VarianceError] =
    trace.force(i"chkVar($tp ${tp.className}) $vVarianceSign", variances) {
      try
        if (status.isDefined) status
        else tp match {
          case tp: TypeRef =>
            val sym = tp.symbol
            if (sym.isOneOf(VarianceFlags) && base.isContainedIn(sym.owner)) checkVarianceOfSymbol(sym)
            else sym.info match {
              case MatchAlias(_) => foldOver(status, tp)
              case TypeAlias(alias) => this(status, alias)
              case _ => foldOver(status, tp)
            }
          case AnnotatedType(_, annot) if annot.symbol == defn.UncheckedVarianceAnnot =>
            //println(i"skipping: $tp")
            status
          case tp: ClassInfo =>
            foldOver(status, tp.parents)
          case TypeBounds(lo, hi) =>
            val x = status
            if lo eq hi then atVariance(0)(this(x, lo))
            else
              variance = -variance
              val y = lo match
                case lo: HKTypeLambda => this(x, lo.resultType)
                case _                => this(x, lo)
              variance = -variance
              val z = hi match
                //case hi: HKTypeLambda => this(x, hi.resultType)
                //case _                => this(x, hi)
                case hi: HKTypeLambda => this(y, hi.resultType)
                case _                => this(y, hi)
              //y.orElse(z)
              z
          case _ =>
            foldOver(status, tp)
        }
      catch {
        case ex: Throwable => handleRecursive("variance check of", tp.show, ex)
      }
    }

    def checkInfo(info: Type): Option[VarianceError] = info match
      case info: MethodOrPoly =>
        checkInfo(info.resultType) // params will be checked in their TypeDef or ValDef nodes.
      case _ =>
        apply(None, info)

    def validateDefinition(base: Symbol): Option[VarianceError] =
    trace.force(i"validateDefinition($base)"):
      val savedBase = this.base
      val savedVariance = variance
      def isLocal =
        base.isAllOf(PrivateLocal)
        || base.is(Private) && !base.hasAnnotation(defn.AssignedNonLocallyAnnot)
      this.base = base
      if base.is(Mutable, butNot = Method) && !isLocal then
        base.removeAnnotation(defn.AssignedNonLocallyAnnot)
        variance = 0
      try checkInfo(base.info)
      finally
        this.base = savedBase
        this.variance = savedVariance
  }

  private object Traverser extends TreeTraverser {
    def checkVariance(sym: Symbol, pos: SrcPos) = Validator.validateDefinition(sym) match {
      case Some(VarianceError(tvar, required)) =>
        def msg =
          val enumAddendum =
            val towner = tvar.owner
            if towner.isAllOf(EnumCase) && towner.isClass && tvar.is(Synthetic) then
              val example =
                "See an example at https://docs.scala-lang.org/scala3/reference/enums/adts.html#parameter-variance-of-enums"
              i"\n${hl("enum case")} ${towner.name} requires explicit declaration of $tvar to resolve this issue.\n$example"
            else
              ""
          em"${varianceLabel(tvar.flags)} $tvar occurs in ${varianceLabel(required)} position in type ${sym.info} of $sym$enumAddendum"
        if (migrateTo3 &&
            (sym.owner.isConstructor || sym.ownersIterator.exists(_.isAllOf(ProtectedLocal))))
          report.migrationWarning(
            msg.prepend("According to new variance rules, this is no longer accepted; need to annotate with @uncheckedVariance\n"),
            pos)
            // patch(Span(pos.end), " @scala.annotation.unchecked.uncheckedVariance")
            // Patch is disabled until two TODOs are solved:
            // TODO use an import or shorten if possible
            // TODO need to use a `:' if annotation is on term
        else report.error(msg, pos)
      case None =>
    }

    override def traverse(tree: Tree)(using Context) = {
      def sym = tree.symbol
      // No variance check for private/protected[this] methods/values.
      def skip = !sym.exists
        || sym.name.is(InlineAccessorName) // TODO: should we exclude all synthetic members?
        || sym.isAllOf(LocalParamAccessor) // local class parameters are construction only
        || sym.is(TypeParam) && sym.owner.isClass // already taken care of in primary constructor of class
      try tree match {
        case defn: MemberDef if skip =>
          report.debuglog(s"Skipping variance check of ${sym.showDcl}")
        case tree: TypeDef =>
          checkVariance(sym, tree.srcPos)
          tree.rhs match {
            case rhs: Template => traverseChildren(rhs)
            case _ =>
          }
        case tree: ValDef =>
          checkVariance(sym, tree.srcPos)
        case DefDef(_, paramss, _, _) =>
          checkVariance(sym, tree.srcPos)
          paramss.foreach(_.foreach(traverse))
        case _ =>
      }
      catch {
        case ex: TypeError => report.error(ex, tree.srcPos.focus)
      }
    }
  }
}
