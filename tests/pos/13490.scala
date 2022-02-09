object MyApi:
  enum MyEnum:
    case A
object Test:
  export MyApi.MyEnum
object Test2:
  import Test.MyEnum.A
  def foo: Any = A


/*

before:
  Test:
    final def MyEnum: MyApi.MyEnum.type = MyApi.MyEnum
    @Child[(MyApi.MyEnum.A : MyApi.MyEnum)] final type MyEnum = MyApi.MyEnum
  Test2:
    def foo: Any = MyApi.MyEnum#A

[[syntax trees at end of                   erasure]] // tests/pos/13490.scala

after:
  Test:
    final def MyEnum(): MyApi.MyEnum = MyApi.MyEnum   // singleton type widened
  Test2:
    def foo(): Object = ((): MyApi.MyEnum)#A

 */
