import StructuralExhaustion.Graph.InducedPathComponentD1D3Ledger

namespace StructuralExhaustion.Examples.ComponentD1D3Ledger

open StructuralExhaustion
open StructuralExhaustion.Graph
open StructuralExhaustion.Graph.InducedPathComponentD1D3Ledger

universe u

variable {V : Type u} {object : FiniteObject V}

/-! Theorem-independent transfer of the cyclic component-state ledger. -/

structure Source (object : FiniteObject V) where
  input : InducedPathComponentD1D3Ledger.Input object

namespace Source

noncomputable def anchorState (source : Source object)
    (LengthOK : Nat → Prop) (lengthOKDecidable : DecidablePred LengthOK) :
    InducedPathComponentD1D3Ledger.State :=
  (InducedPathComponentD1D3Observation.run source.input.base LengthOK
    lengthOKDecidable).value

noncomputable def result (source : Source object)
    (LengthOK : Nat → Prop) (lengthOKDecidable : DecidablePred LengthOK) :=
  InducedPathComponentD1D3Ledger.run source.input
    (source.anchorState LengthOK lengthOKDecidable) LengthOK lengthOKDecidable

theorem result_exhaustive (source : Source object)
    (LengthOK : Nat → Prop) (lengthOKDecidable : DecidablePred LengthOK) :
    (∃ repetition, source.result LengthOK lengthOKDecidable =
        .repeated repetition) ∨
      (∃ codesNodup lengthLe, source.result LengthOK lengthOKDecidable =
        .bounded codesNodup lengthLe) := by
  cases equation : source.result LengthOK lengthOKDecidable with
  | repeated repetition => exact Or.inl ⟨repetition, rfl⟩
  | bounded codesNodup lengthLe =>
      exact Or.inr ⟨codesNodup, lengthLe, rfl⟩

theorem exact_state_card (_source : Source object) :
    Fintype.card InducedPathComponentD1D3Ledger.State =
      4 ^ 2 * 13 ^ 2 * 2 ^ 13 :=
  InducedPathComponentD1D3Ledger.stateCard

theorem anchor_agrees_with_one_state (source : Source object)
    (LengthOK : Nat → Prop) (lengthOKDecidable : DecidablePred LengthOK) :
    (InducedPathComponentD1D3Ledger.observation source.input LengthOK
        lengthOKDecidable
        (InducedPathComponentD1D3Ledger.anchorStub source.input)).value =
      (InducedPathComponentD1D3Observation.run source.input.base LengthOK
        lengthOKDecidable).value :=
  InducedPathComponentD1D3Ledger.anchor_observation_eq source.input
    LengthOK lengthOKDecidable

theorem local_work_polynomial (source : Source object) :
    InducedPathComponentD1D3Ledger.visibleChecks source.input ≤
      100 * InducedPathComponentD1D3Ledger.localScale source.input ^ 4 :=
  InducedPathComponentD1D3Ledger.visibleChecks_polynomial source.input

end Source

end StructuralExhaustion.Examples.ComponentD1D3Ledger
