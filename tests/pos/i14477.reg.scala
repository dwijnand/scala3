def foo[T](xs: List[T]): T = xs match {
  case xs: List[u] =>
    val head: u = xs.head
    val head2: T = head
    head2
}
