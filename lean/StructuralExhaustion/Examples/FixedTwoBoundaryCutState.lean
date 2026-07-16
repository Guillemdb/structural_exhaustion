import StructuralExhaustion.Core.FixedTwoBoundaryCutState

namespace StructuralExhaustion.Examples.FixedTwoBoundaryCutState

open Core.FixedTwoBoundaryCutState

@[reducible] def evenLength (length : Nat) : Prop := length % 2 = 0

@[reducible] def evenLengthDecidable : DecidablePred evenLength :=
  fun _ ↦ inferInstance

/-- A completely unrelated finite prefix system exercises the reusable
projection without any Erdős-specific graph type. -/
def observations : PrefixObservations Nat where
  boundaryDegree segment role := segment + role.val
  windowOffset segment role := ⟨(segment + role.val) % 13, Nat.mod_lt _ (by decide)⟩
  connectorLength segment := segment

def localProjection : LocalProjection Nat (Fin 5) where
  response segment coordinate := decide (coordinate.val ≤ segment)

def code (segment : Nat) : State (Fin 5) :=
  project evenLength evenLengthDecidable observations localProjection segment

example : (code 7).boundaryDegree 0 = capDegree 7 := rfl

example : (code 7).targetResponse 3 = true := by
  rfl

example : Fintype.card (State (Fin 5)) =
    4 ^ 2 * 13 ^ 2 * 2 ^ 13 * 2 ^ 5 := by
  simpa using state_card (Fin 5)

example : Fintype.card (StateFor (Fin 3) (Fin 5)) =
    Fintype.card (StateFor (Fin 1000) (Fin 5)) :=
  state_card_independent_of_ambient (Fin 3) (Fin 1000) (Fin 5)

def declaredTargetResponse (segment context : Nat) : Bool :=
  decide (segment ≤ context)

example :
    EqualCodeComparison localProjection Nat declaredTargetResponse 7 7 :=
  compareEqualCodes evenLength evenLengthDecidable observations localProjection
    Nat declaredTargetResponse 7 7 (.inr ⟨fun _ ↦ rfl⟩) rfl

end StructuralExhaustion.Examples.FixedTwoBoundaryCutState
