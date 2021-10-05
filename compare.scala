enum Exhausted[S, A]:
  def parse(): A = this match { case Resume(p) => p.parse() }
  case Resume[A](parser: Exhausted[S, S]) extends Exhausted[S, S]

enum Exhausted[S, A]:
  def parse(): A = this match { case Resume(p) => p.parse() }
  case Resume[S, A](parser: Exhausted[A, A]) extends Exhausted[S, A]

(_: Exhausted[S, A]) match
  case Resume.unapply[S   ](p): Resume[S   ] => p.parse().$asInstanceOf[A]
  case Resume.unapply[S, A](p): Resume[S, A] => p.parse()

Resume.unapply: [S   ](x: Resume[S   ]): Resume[S   ]
Resume.unapply: [S, A](x: Resume[S, A]): Resume[S, A]

Resume.unapply[S   ](p): Resume[S   ] ====> Prod(Resume[S   ], Typ(Exhausted[S, S])
Resume.unapply[S, A](p): Resume[S, A] ====> Prod(Resume[S, A], Typ(Exhausted[A, A])

signature of Resume.unapply ----> Exhausted[Nothing, Nothing]
signature of Resume.unapply ----> Exhausted[A, A]

Exhausted[S, A]             decomposes to [Resume[<?>]]
Exhausted[S, A]             decomposes to [Resume[S, A]]

Exhausted[Nothing, Nothing] decomposes to [Resume[Nothing]]
Exhausted[S, S]             decomposes to [Resume[S]]
Exhausted[A, A]             decomposes to [Resume[A, A]]

uncovered Prod(Exhausted.Resume[<?>], Typ(Exhausted[Nothing, Nothing]))
