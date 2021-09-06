trait T {
  sealed trait A
  object A {
    case object B extends A
  }
}
object O extends T
case object C extends O.A
