import Mathlib.Tactic
import StructuralExhaustion.Core.FinitePredicateAlignment
import StructuralExhaustion.CT10.ExhaustiveClassification

namespace StructuralExhaustion.Examples.FinitePredicateAlignment

open StructuralExhaustion

def alignedProfile : Core.FinitePredicateAlignment.Profile where
  Coordinate := Fin 3
  coordinates := inferInstance
  left := fun coordinate => coordinate.val < 2
  right := fun coordinate => coordinate.val ≠ 2
  leftDecidable := fun _ => inferInstance
  rightDecidable := fun _ => inferInstance

example : ∀ coordinate,
    alignedProfile.left coordinate ↔ alignedProfile.right coordinate := by
  intro coordinate
  rcases coordinate with ⟨value, bound⟩
  interval_cases value <;> simp [alignedProfile]

example := alignedProfile.decide_total

def mismatchedProfile : Core.FinitePredicateAlignment.Profile where
  Coordinate := Bool
  coordinates := Core.Enumeration.bool
  left := fun value => value = true
  right := fun _ => False
  leftDecidable := fun _ => inferInstance
  rightDecidable := fun _ => inferInstance

example : mismatchedProfile.Mismatch true := by
  simp [Core.FinitePredicateAlignment.Profile.Mismatch, mismatchedProfile]

example := mismatchedProfile.decide_total

example : mismatchedProfile.checks = 2 := by native_decide

/-! The same CT10 coupling used by the graph classifier, on a
theorem-independent two-coordinate fixture.  The accepted CT10 class is the
tag computed from the actual alignment decision, not a caller-supplied or
always-true class table. -/

abbrev problem : Core.Problem where
  Ambient := Unit
  Baseline := fun _ => True
  rank := fun _ => 0
  BranchState := fun _ => Unit

def context : Core.BranchContext problem := ⟨(), trivial, ()⟩

noncomputable def decisionTag : Bool :=
  match mismatchedProfile.decide with
  | .mismatch _ => true
  | .aligned _ => false

noncomputable def decisionTagProfile :
    CT10.ExhaustiveClassification.Profile Bool :=
  CT10.ExhaustiveClassification.Profile.exactSelection
    Core.Enumeration.bool decisionTag

noncomputable def decisionTagStage :=
  decisionTagProfile.verifiedStage context

example : decisionTagProfile.Accepts decisionTag := rfl

example : decisionTagProfile.checks = 4 := by
  rw [decisionTagProfile,
    CT10.ExhaustiveClassification.Profile.exactSelection_checks]
  rfl

example : (decisionTagProfile.run context).terminal = .exhaustive :=
  decisionTagStage.terminal

example : (decisionTagProfile.run context).trace =
    [.entry, .table, .direct, .missing, .exhaustiveTerminal] :=
  decisionTagStage.trace

example : (decisionTagProfile.run context).outcome.Valid :=
  decisionTagStage.verified

example := decisionTagStage.traceValid
example := decisionTagStage.total

end StructuralExhaustion.Examples.FinitePredicateAlignment
