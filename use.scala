def test1[S, A](foo: t1.Foo[S, A]): A = foo match
  case t1.Foo.Resume(foo) => test1(foo)

def test2[S, A](foo: t2.Foo[S, A]): A = foo match
  case t2.Foo.Resume(foo) => test2(foo)
