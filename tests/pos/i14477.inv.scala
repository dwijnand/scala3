class MutableBox[T] (var value: T) 

def foo[T](xs: MutableBox[T]): T = xs match {
  case xs: MutableBox[u] =>
    val head: u = xs.value
    head
}
