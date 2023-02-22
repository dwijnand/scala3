/*

Change the context so that instead of a GadtConstraint
it just contains a map from symbols to infos.

TypeComparer would consult that map and, if a symbol has an entry,
try that entry for comparisons.

The entry could be a type variable linked to a GadtConstraint,
but that's the business of Typer. Context knows nothing about this.

*/

sealed trait Expr[T]
case class BoolExpr(v: Boolean) extends Expr[Boolean]
case class IntExpr(v: Int)      extends Expr[Int]

class Test:
  def mat1[X](x: Expr[X]) = // GadtState#1  X [Nothing..Any]
    x match
      case BoolExpr(v) => 1 // GadtState#2  X [Nothing..Boolean] // snap1
      case IntExpr(v)  => 2 // GadtState#3  X [Nothing..Int]     // snap2

//    Context -> GadtState/GadtConstraint -> Symbol 1 / LB / UB
//                                        -> Symbol 2 / LB / UB

//    Context -> Symbol 1 -> GadtTypeVar -> GadtState#1 -> Symbol 1 / LB / UB
//            -> Symbol 2 -> GadtTypeVar -> GadtState#2
