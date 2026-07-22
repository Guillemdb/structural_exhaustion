import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

/-!
# Finite triangular index families

`Pair bound` is the generic schedule of ordered nonnegative pairs whose sum is
strictly below `bound`.  Applications may reinterpret coordinates by adding
one, but the core structure is theorem-independent.
-/

namespace Hypostructure.Core.FiniteTriangle

/-- Ordered finite pairs below a strict sum bound. -/
abbrev Pair (bound : Nat) :=
  {candidate : Fin bound × Fin bound //
    candidate.1.1 + candidate.2.1 < bound}

namespace Pair

def left {bound : Nat} (pair : Pair bound) : Nat :=
  pair.1.1.1

def right {bound : Nat} (pair : Pair bound) : Nat :=
  pair.1.2.1

theorem sum_lt {bound : Nat} (pair : Pair bound) :
    pair.left + pair.right < bound :=
  pair.2

end Pair

end Hypostructure.Core.FiniteTriangle
