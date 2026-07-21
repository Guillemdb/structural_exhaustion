import Hypostructure.Graph.Object

/-!
# Minimal graph problem registration

`Graph.problem` is defined beside `FiniteObject` so lower graph modules can use
the registration without importing any optional capability.  This module is
the canonical public import for that registration.  The target remains a
separate predicate and is intentionally absent from every declaration here.
-/

namespace Hypostructure.Graph

universe u v

@[simp]
theorem problem_baseline (Baseline : FiniteObject.{u} -> Prop)
    (BranchState : FiniteObject.{u} -> Type v) (object : FiniteObject.{u}) :
    (problem Baseline BranchState).Baseline object = Baseline object :=
  rfl

@[simp]
theorem problem_branchState (Baseline : FiniteObject.{u} -> Prop)
    (BranchState : FiniteObject.{u} -> Type v) (object : FiniteObject.{u}) :
    (problem Baseline BranchState).BranchState object = BranchState object :=
  rfl

end Hypostructure.Graph
