sealed trait Foo[X <: A, A]

type FooX[F] = F match {
  case Foo[x, a] => x
}

val hello: FooX[Foo["hello", String]] = "hello"
