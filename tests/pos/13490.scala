object MyApi:
  enum MyEnum:
    case A
object Test:
  export MyApi.MyEnum
object Test2:
  import Test.MyEnum.A
  def foo: Any = A

/*

if we avoid the export by doing `import MyApi.MyEnum.A` directly,
after typer foo still looks like:

  def foo: Any = MyApi.MyEnum#A

so either the `#` thing is correct, or it's wrong somehow but without
it ending up mattering (?)

or perhaps the `#` thing is a printer bug and we're reading too much into it

 */

/*

after typer:
  Test2:
    import Test.MyEnum.A
    def foo: Any = MyApi.MyEnum#A



just before erasure:
  Test:
    final def MyEnum: MyApi.MyEnum.type = MyApi.MyEnum
    @Child[(MyApi.MyEnum.A : MyApi.MyEnum)] final type MyEnum = MyApi.MyEnum
  Test2:
    def foo: Any = MyApi.MyEnum#A      // why is it `#` rather than `.`?
                                       // this seems especially weird since A isn't an inner class, it's just a term
                                       //    case <static> val A: MyApi.MyEnum = MyApi.MyEnum.$new(0, "A")

[[syntax trees at end of                   erasure]]

after:
  Test:
    final def MyEnum(): MyApi.MyEnum = MyApi.MyEnum   // forwarder made by `export`; singleton type widened (?!)
  Test2:
    def foo(): Object = ((): MyApi.MyEnum)#A

// and then later...

[[syntax trees at end of MegaPhase{dropOuterAccessors, checkNoSuperThis, flatten, transformWildcards, moveStatic, expandPrivate, restoreScopes, selectStatic, Collect entry points, collectSuperCalls, repeatableAnnotations}]]

  Test2:
    def foo(): Object = ((): MyApi.MyApi$MyEnum)#A



one hypothesis is that the `(): MyApi.MyEnum` thing is crazy and that's the bug
we looked at the crash briefly and it plausibly seems that yes, it's trying to do something with Unit
  (and that makes no sense)

*/



/*
we're println debugging in Erasure.scala.

before erasure:
  DefDef(
    foo,
    List(),
    TypeTree[TypeRef(TermRef(ThisType(TypeRef(NoPrefix,module class <root>)),object scala),class Any)],
    Ident(A)))))))
after erasure:
  DefDef(
    foo,
    List(List()),
    TypeTree[TypeRef(ThisType(TypeRef(NoPrefix,module class lang)),class Object)],
    Ident(A)))))))

