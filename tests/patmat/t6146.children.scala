// Let's test other orders...  We had the first one above, and we'll test the others next:
//   1) 1 2 3: traits - objects - outsider  (T1/T2, O1/O2, Shorty) // match case unreachable
//   2) 1 3 2: traits - outsider - objects                         // match case unreachable
//   3) 2 1 3: objects - traits  - outsider                        // match case unreachable
//   4) 2 3 1: objects - outsider - traits
//   5) 3 1 2: outsider - traits - objects
//   6) 3 2 1: outsider - objects - traits
// Conclusion: if the outsider comes after the trait, the match in unreachable

trait T1[X] { sealed trait A; object A { case object B extends A } }
object O1 extends T1[Any]
case object C1 extends O1.A

trait T2[X] { sealed trait A; object A { case object B extends A } }
case object C2 extends O2.A
object O2 extends T2[Any]

object O3 extends T3[Any]
trait T3[X] { sealed trait A; object A { case object B extends A } }
case object C3 extends O3.A

object O4 extends T4[Any]
case object C4 extends O4.A
trait T4[X] { sealed trait A; object A { case object B extends A } }

case object C5 extends O5.A
trait T5[X] { sealed trait A; object A { case object B extends A } }
object O5 extends T5[Any]

case object C6 extends O6.A
object O6 extends T6[Any]
trait T6[X] { sealed trait A; object A { case object B extends A } }
