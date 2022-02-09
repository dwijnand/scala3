object MyApi:
  enum MyEnum:
    case A
object Test:
  export MyApi.MyEnum
object Test2:
  import Test.MyEnum.A
  def foo: Any = A
