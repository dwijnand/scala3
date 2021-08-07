import scala.language.strictUnsealedPatmat

class Foo {
  def foo(x: quoted.Expr[Int])(using scala.quoted.Quotes): Unit = x match {
    case '{ 1 } =>
    case '{ 2 } =>
  }
}
