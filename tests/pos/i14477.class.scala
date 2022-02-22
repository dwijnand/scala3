class Foo[A >: Nothing <: Any, X >: Nothing <: A]

type FooX[F] = F match {
  case Foo[a, x] => x
}

val hello: FooX[Foo[Int, Int]] = 1