sealed trait Foo[A]
final case class Bar(value: String) extends Foo[String]

object Example {
  def whatthe(x: Foo[Unit]): Unit = x match
    case Bar(_) =>
}
