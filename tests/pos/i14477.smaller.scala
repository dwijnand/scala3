sealed trait Foo[A, X <: A]

type FooX[F] = F match {
  case Foo[a, x] => x
}

val hello: FooX[Foo[String, "hello"]] = "hello"
