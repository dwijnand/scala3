object Test {
  sealed trait Base
  sealed class Blub extends Base
  object Blub {
    def unapply(blub: Blub): Some[(Int, blub.type)] =
      Some(1 -> blub)
  }

  (null: Base) match {
    case b: Blub => b match {
      case Blub(i, x) => println(i)
    }
  }
}
