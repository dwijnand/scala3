sealed trait Foo[X]
final case class Bar[Y](value: Y) extends Foo[Y]

class Test:
  def test[T](foo: Foo[T]): T = foo match
    case Bar/*[?Y]*/(value) => value
