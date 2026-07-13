import StructuralExhaustion.Core.AutomationFirst

namespace StructuralExhaustion.CT15

universe uAmbient uBranch uCoordinate

/-!
Primitive target-relative rank semantics.

The proof instance defines only what a coordinate is, when it is dependent
relative to the target, its forced full-rank charge, and the available branch
capacity.  Rank, ledgers, comparisons, residuals, and outcomes are all
framework computations.
-/

structure Spec (P : Core.Problem.{uAmbient, uBranch}) where
  Coordinate : Type uCoordinate
  TargetDependent : Core.BranchContext P → Coordinate → Prop
  charge : Core.BranchContext P → Coordinate → Nat
  capacity : Core.BranchContext P → Nat

end StructuralExhaustion.CT15
