package my {
  object MyTypes:
    enum MyEnum:
      case Foo
      case Bar

  object MyApi:
    export MyTypes.*
}

object Test:
  import my.MyApi.MyEnum.Foo
  def foo: Unit =
    val res: Any = Foo
    ()
