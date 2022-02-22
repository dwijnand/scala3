sealed trait Foo[A, X <: A]

type FooX[F] = F match {
  case Foo[a, x] => x
}

val hello: FooX[Foo[String, "hello"]] = "hello"

def regularMatch(foo: Foo[A, B] = match {
  case _: Foo[a1, x1] =>
    val x2: x1 = 
