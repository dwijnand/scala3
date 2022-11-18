package foo {
  class C { override def toString = "1" }
}

package bar {
  class C { override def toString = "2" }
}


object Main:
  def main(args: Array[String]): Unit =
    //println(io.foo.Bar.baz)
    println(io.Codec.UTF8)
