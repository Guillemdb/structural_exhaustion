import Hypostructure.Core.Context
import Hypostructure.Core.SemanticEquivalence

/-!
# Domain-neutral Core primitive fixtures

These fixtures exercise the irreducible problem kernel, optional natural and
lexicographic progress, dependent branch state, minimality, equality and finite
relabeling semantics, and an additive gauge quotient.
-/

namespace Hypostructure.Fixtures.CorePrimitives

open Hypostructure.Core

/-! ## One problem, two targets, and dependent branch state -/

abbrev dependentProblem : Problem where
  Ambient := Nat
  Baseline := fun _ => True
  BranchState := fun n => Fin (n + 1)

def zeroTarget (n : Nat) : Prop := n = 0

def evenTarget (n : Nat) : Prop := Even n

def dependentContext : BranchContext dependentProblem where
  G := 2
  baseline := trivial
  state := ⟨1, by decide⟩

def zeroAvoidingContext : AvoidingContext dependentProblem zeroTarget :=
  AvoidingContext.ofBranch dependentContext (by
    intro target
    change (2 : Nat) = 0 at target
    exact Nat.noConfusion target)

def evenAvoidingContext : AvoidingContext dependentProblem evenTarget where
  toBranchContext := {
    G := 3
    baseline := trivial
    state := ⟨1, by decide⟩
  }
  avoids := by
    change Not (Even 3)
    decide

/-- This Core operation has no progress argument or inferred progress instance. -/
def noProgressStep {P : Problem} (ctx : BranchContext P) : BranchContext P :=
  ctx

example : (noProgressStep dependentContext).G = 2 := rfl

/-! ## Natural and lexicographic progress -/

def naturalProgress : Progress dependentProblem where
  Measure := Nat
  lt := (· < ·)
  wellFounded := wellFounded_lt
  measure := id

example : naturalProgress.Smaller 1 2 := by
  change 1 < 2
  decide

theorem natural_non_strict_replacement_rejected (n : Nat) :
    Not (naturalProgress.Smaller n n) :=
  naturalProgress.not_smaller_self n

abbrev pairProblem : Problem where
  Ambient := Nat × Nat
  Baseline := fun _ => True
  BranchState := fun _ => Unit

def lexicographicProgress : Progress pairProblem where
  Measure := Nat × Nat
  lt := Prod.Lex (· < ·) (· < ·)
  wellFounded := wellFounded_lt.prod_lex wellFounded_lt
  measure := id

example : lexicographicProgress.Smaller (1, 7) (2, 0) := by
  exact Prod.Lex.left _ _ (by decide)

/-! ## Minimal contexts and generic smaller-object closure -/

def oneMinimal :
    MinimalCounterexampleContext dependentProblem zeroTarget naturalProgress :=
  MinimalCounterexampleContext.ofAvoiding
    (AvoidingContext.ofBranch
      ({ G := 1, baseline := trivial, state := ⟨0, by decide⟩ } :
        BranchContext dependentProblem)
      (by
        intro target
        change (1 : Nat) = 0 at target
        exact Nat.noConfusion target))
    (by
      intro H smaller _baseline
      change H < 1 at smaller
      change H = 0
      exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ smaller))

theorem smaller_zero_branch_is_impossible
    (candidate : AvoidingContext dependentProblem zeroTarget)
    (smaller : naturalProgress.Smaller candidate.G oneMinimal.G) : False :=
  oneMinimal.contradiction_of_smaller candidate smaller

theorem a_minimal_context_exists :
    Nonempty
      (MinimalCounterexampleContext dependentProblem zeroTarget naturalProgress) :=
  zeroAvoidingContext.exists_minimalCounterexample naturalProgress
    (fun n => ⟨0, Nat.zero_lt_succ n⟩)

/-! ## Equality and finite relabeling semantics -/

def equalitySemantics : SemanticEquivalence dependentProblem :=
  SemanticEquivalence.equality dependentProblem

def zeroEqualityInvariant : TargetInvariant equalitySemantics zeroTarget :=
  TargetInvariant.equality dependentProblem zeroTarget

abbrev RelabeledPair := Bool × Bool

def relabelingEquivalent (x y : RelabeledPair) : Prop :=
  x = y ∨ x = (y.2, y.1)

def relabelingBaseline (x : RelabeledPair) : Prop :=
  x.1 || x.2 = true

def relabelingTarget (x : RelabeledPair) : Prop :=
  x.1 = x.2

abbrev relabelingProblem : Problem where
  Ambient := RelabeledPair
  Baseline := relabelingBaseline
  BranchState := fun _ => Unit

def relabelingSemantics : SemanticEquivalence relabelingProblem where
  equivalent := relabelingEquivalent
  equivalence := by
    constructor
    · intro x
      exact Or.inl rfl
    · intro x y equivalent
      rcases equivalent with rfl | equivalent
      · exact Or.inl rfl
      · right
        rw [equivalent]
    · intro x y z first second
      rcases first with rfl | first
      · exact second
      · rcases second with rfl | second
        · exact Or.inr first
        · left
          rw [first, second]
  baseline_iff := by
    intro G H equivalent
    rcases equivalent with rfl | equivalent
    · rfl
    · rw [equivalent]
      simp [relabelingBaseline, Bool.or_comm]

def relabelingTargetInvariant :
    TargetInvariant relabelingSemantics relabelingTarget where
  target_iff := by
    intro G H equivalent
    rcases equivalent with rfl | equivalent
    · rfl
    · rw [equivalent]
      simp [relabelingTarget, eq_comm]

example : relabelingSemantics.equivalent (true, false) (false, true) :=
  Or.inr rfl

/-! ## Additive quotient semantics -/

abbrev GaugePair := Int × Int

def gaugeEquivalent (x y : GaugePair) : Prop :=
  x.1 - x.2 = y.1 - y.2

def gaugeBaseline (x : GaugePair) : Prop :=
  0 <= x.1 - x.2

def gaugeTarget (x : GaugePair) : Prop :=
  x.1 - x.2 = 0

def gaugeBadTarget (x : GaugePair) : Prop :=
  x.1 = 0

abbrev gaugeProblem : Problem where
  Ambient := GaugePair
  Baseline := gaugeBaseline
  BranchState := fun _ => Unit

def gaugeSemantics : SemanticEquivalence gaugeProblem where
  equivalent := gaugeEquivalent
  equivalence := by
    constructor
    · intro x
      rfl
    · intro x y equivalent
      exact equivalent.symm
    · intro x y z first second
      exact first.trans second
  baseline_iff := by
    intro G H equivalent
    change (0 <= G.1 - G.2) ↔ (0 <= H.1 - H.2)
    rw [equivalent]

def gaugeTargetInvariant : TargetInvariant gaugeSemantics gaugeTarget where
  target_iff := by
    intro G H equivalent
    unfold gaugeTarget
    rw [equivalent]

example (x : GaugePair) (shift : Int) :
    gaugeSemantics.equivalent x (x.1 + shift, x.2 + shift) := by
  change x.1 - x.2 = (x.1 + shift) - (x.2 + shift)
  omega

/-- The first coordinate does not descend to the additive gauge quotient. -/
theorem gaugeBadTarget_not_invariant :
    Not (TargetInvariant gaugeSemantics gaugeBadTarget) := by
  intro invariant
  have equivalent : gaugeSemantics.equivalent
      ((0, 0) : GaugePair) ((1, 1) : GaugePair) := by
    rfl
  have targetAtZero : gaugeBadTarget ((0, 0) : GaugePair) := rfl
  have targetAtOne : gaugeBadTarget ((1, 1) : GaugePair) :=
    (invariant.target_iff equivalent).mp targetAtZero
  exact Int.one_ne_zero targetAtOne

#print axioms natural_non_strict_replacement_rejected
#print axioms smaller_zero_branch_is_impossible
#print axioms a_minimal_context_exists
#print axioms gaugeBadTarget_not_invariant

end Hypostructure.Fixtures.CorePrimitives
