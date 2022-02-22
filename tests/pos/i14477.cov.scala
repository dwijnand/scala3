case class ImmutableBox[+A](value: A)

def foo[T](xs: ImmutableBox[T]): T = xs match {
  case xs: ImmutableBox[u] =>
    val value: u = xs.value
    val value2: T = value
    value2
}
