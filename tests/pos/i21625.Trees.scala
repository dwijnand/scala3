object Trees:
  class Type
  type Untyped = Type | Null
  abstract class Tree[+T <: Untyped]():
    def orElse[U >: T <: Untyped](that: Tree[U]): Tree[U] = that
