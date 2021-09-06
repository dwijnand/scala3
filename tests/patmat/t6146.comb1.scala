trait T[X] {
  sealed trait A
  object A {
    case object B extends A
  }
}
object O extends T[Any]
case object C extends O.A
