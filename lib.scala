package t1:
  enum Foo[S, A]:
    case Resume[S, A](foo: Foo[A, A]) extends Foo[A, A]

package t2:
  enum Foo[S, A]:
    case Resume[S, A](foo: Foo[A, A]) extends Foo[S, A]
