sealed trait Foo[A]
final case class Bar(value: String) extends Foo[String]

object Example {
  def whatthe[A, B]: Foo[A => B] => Unit = {
    case Bar(_) => ()
  }
}
