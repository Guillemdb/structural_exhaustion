import Hypostructure.Core.Prelude

/-!
# Mathematical resource budgets

`ResourceBudget` describes the ordered additive resource used by a proof.  It
does not count verifier operations; executable work uses
`PolynomialCheckBudget` instead.
-/

namespace Hypostructure.Core

universe u v

/-- Ordered additive data sufficient for framework-owned resource accounting. -/
structure ResourceBudget where
  Resource : Type u
  le : Resource -> Resource -> Prop
  leRefl : forall r, le r r
  leTrans : forall {a b c}, le a b -> le b c -> le a c
  zero : Resource
  add : Resource -> Resource -> Resource
  ceiling : Nat -> Resource
  zeroLe : forall r, le zero r
  addMono : forall {a b c d}, le a b -> le c d -> le (add a c) (add b d)
  addAssoc : forall a b c, add (add a b) c = add a (add b c)
  zeroAdd : forall a, add zero a = a
  addZero : forall a, add a zero = a

namespace ResourceBudget

instance (B : ResourceBudget) : LE B.Resource := ⟨B.le⟩

theorem add_le_add (B : ResourceBudget) {a b c d : B.Resource}
    (hab : a <= b) (hcd : c <= d) : B.add a c <= B.add b d :=
  B.addMono hab hcd

/-- Fold a finite resource schedule using the budget's own addition. -/
def sum (B : ResourceBudget) : List B.Resource -> B.Resource
  | [] => B.zero
  | r :: rs => B.add r (sum B rs)

@[simp] theorem sum_nil (B : ResourceBudget) : sum B [] = B.zero := rfl

@[simp] theorem sum_cons (B : ResourceBudget) (r : B.Resource)
    (rs : List B.Resource) : sum B (r :: rs) = B.add r (sum B rs) := rfl

/-- Pointwise domination implies domination of the framework fold. -/
theorem sum_le_sum (B : ResourceBudget) {xs ys : List B.Resource}
    (h : List.Forall₂ (fun x y => x <= y) xs ys) :
    sum B xs <= sum B ys := by
  induction h with
  | nil => exact B.leRefl B.zero
  | cons hab _ ih => exact B.addMono hab ih

end ResourceBudget

/-- A represented cost is invariant under the domain's semantic equivalence. -/
structure ResourceRepresentationInvariant (B : ResourceBudget)
    (Object : Type v) (Equivalent : Object -> Object -> Prop) where
  cost : Object -> B.Resource
  cost_eq : forall {left right}, Equivalent left right -> cost left = cost right

/-- A local static bound is comparable with a dynamic resource transcript. -/
structure StaticDynamicComparison (B : ResourceBudget)
    (Static Dynamic : Type v) where
  staticCost : Static -> B.Resource
  dynamicCost : Dynamic -> B.Resource
  comparable : Static -> Dynamic -> Prop
  transfer : forall {s d}, comparable s d -> dynamicCost d <= staticCost s

end Hypostructure.Core
