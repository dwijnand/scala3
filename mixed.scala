trait Animal
trait Pet extends Animal
trait Cat extends Pet
trait Bae extends Cat

trait F1[T1 >: Cat]
trait F2[T2 >: Cat] extends F1[T2]
trait F3[T3 >: Cat] extends F2[T3]

/*
trait Cov[+B]:
  def getA[A >: B](    ): A
  def getB        (    ): B
//def getC[C <: B](    ): C    // error: C <: B
  def setA[A >: B](x: A): Unit
//def setB        (x: B): Unit // error: x: B
//def setC[C <: B](x: C): Unit // error: C <: B

  def modAA[A >: B](x: A): A
  def modAB[A >: B](x: A): B
//def modBA[A >: B](x: B): A   // error: x: B
//def modBB        (x: B): B   // error: x: B
//def modBC[C <: B](x: B): C   // error: C <: B // error: x: B
//def modCB[C <: B](x: C): B   // error: C <: B
//def modCC[C <: B](x: C): C   // error: C <: B

trait Con[-Y]:
  def setZ[Z <: Y](x: Z): Unit
  def setY        (x: Y): Unit
//def setX[X >: Y](x: X): Unit // error: X >: Y
  def getZ[Z <: Y](    ): Z
//def getY        (    ): Y    // error: (): Y
//def getX[X >: Y](    ): X    // error: X >: Y

  def modZZ[Z <: Y](x: Z): Z
  def modYZ[Z <: Y](x: Y): Z
//def modZY[Z <: Y](x: Z): Y   // error: [..): Y
//def modYY        (x: Y): Y   // error: (..): Y
//def modXY[X >: Y](x: X): Y   // error: [..): Y
//def modYX[X >: Y](x: Y): X   // error: X >: Y
//def modXX[X >: Y](x: X): X   // error: X >: Y
*/

trait Foo[-Y]:
  def k1[F[y1 >: Y], G[y2 >: Y] >: H[y2] <: F[y2], H[y3 >: Y]]: Unit

class Test:
  def test(p: Foo[Cat]): Unit =
    p.k1[F1, F2, F3]
    ()
