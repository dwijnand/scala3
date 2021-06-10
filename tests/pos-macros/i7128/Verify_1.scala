// Verify.scala
import scala.language.experimental.macros
import scala.quoted.*

class Runtime {
  def fooValue[U](u: U): U = ???
}

class Macro(using qctx: Quotes) {
  import qctx.reflect._

  def apply[A: Type](x: Expr[A]): Expr[Unit] = {
    val termArg = x.asTerm.underlyingArgument.asExprOf[A]
    '{
      val rt: Runtime = ???
      ${Block(doExprs('{ rt }.asTerm, termArg.asTerm), '{ () }.asTerm).asExprOf[Unit]}
    }
  }

  private def doExprs(rt: Term, t: Term): List[Term] = doAllVals(rt, t) :: Nil

  private def doAllVals(rt: Term, t: Term): Term = doVal(rt, doSubVals(rt, t))

  private def doSubVals(rt: Term, t: Term): Term = t match {
    case Apply(x, ys) => Apply(doAllVals(rt, x), ys.map(doAllVals(rt, _)))
    case _            => t
  }

  private val runtimeSym: Symbol = TypeRepr.of[Runtime].typeSymbol

  private def doVal(rt: Term, t: Term): Term = t match {
    case TypeApply(_, _) => t
    case _ =>
      val sel: Term = rt.select(runtimeSym.memberMethod("fooValue").head)
      Apply.copy(t)(sel.appliedToType(t.tpe), t :: Nil)
  }
}

object Macro {
  def apply[A: Type](x: Expr[A])(using Quotes): Expr[Unit] =
    new Macro().apply(x)
}

class Assert[A] {
  inline def apply(value: A): Unit = ${ Macro.apply('value) }
}

trait TestSuite {
  def assert: Assert[Boolean] = ???
  def test(f: => Unit): Unit = ???
}
