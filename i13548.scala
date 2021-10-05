enum Exhausted[S, A]:
  def parse(input: String, offset: Int): A = this match
    case Resume(p) => p.parse(input, offset)

  case Resume[S, A](parser: Exhausted[A, A]) extends Exhausted[A, A]
