// Main.scala
object N
type T[A] >: N.type

object Test extends TestSuite {
  test {
    def foo(x: T[Int]): Boolean = ???
    def boom = assert(foo(N))
  }
}
