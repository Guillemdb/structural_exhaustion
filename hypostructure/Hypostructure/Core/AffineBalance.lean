import Mathlib.Tactic

/-!
# Domain-neutral affine balance elimination

Core owns only the algebraic elimination of one conserved balance and one
rank/defect relation.  Graph and PDE contracts supply the meanings of the
quantities and their exact identities.
-/

namespace Hypostructure.Core.AffineBalance

theorem eliminate
    {coefficient internal surplus boundary total rank offset : Int}
    (balance : coefficient * internal + surplus + boundary = 2 * total)
    (rank_eq : rank = total - internal - boundary + offset) :
    (coefficient - 2) * internal =
      2 * rank + boundary - surplus - 2 * offset := by
  linarith

theorem solve_one_three
    {internal surplus boundary total rank : Int}
    (balance : 3 * internal + surplus + boundary = 2 * total)
    (rank_eq : rank = total - internal - boundary + 1) :
    internal = boundary - 2 + 2 * rank - surplus := by
  linarith

end Hypostructure.Core.AffineBalance
