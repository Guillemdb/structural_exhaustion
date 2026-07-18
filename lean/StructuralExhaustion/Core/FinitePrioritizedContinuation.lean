import StructuralExhaustion.Core.FiniteFirstFailure

namespace StructuralExhaustion.Core.FinitePrioritizedContinuation

open StructuralExhaustion

universe uStage uF1 uF2 uF3 uF4 uGerm

/-!
# A one-source prioritized continuation profile

This reusable adapter executes F1--F4 in stage-major order through
`FiniteFirstFailure`.  Later semantics are explicit local predicates; the F5
constructor receives exhaustive negative evidence for every predicate at
every declared stage.
-/

structure LaterSemantics (Stage : Type uStage) (F1 : Stage → Prop) where
  F2 : Stage → Prop
  F3 : Stage → Prop
  F4 : Stage → Prop
  f2Decidable : ∀ stage, Decidable (F2 stage)
  f3Decidable : ∀ stage, Decidable (F3 stage)
  f4Decidable : ∀ stage, Decidable (F4 stage)
  F2Data : Type uF2
  F3Data : Type uF3
  F4Data : Type uF4
  f2Data : ∀ stage, F2 stage → F2Data
  f3Data : ∀ stage, F3 stage → F3Data
  f4Data : ∀ stage, F4 stage → F4Data
  Germ : Type uGerm
  germOfClear : ∀ schedule : List Stage,
    (∀ stage, stage ∈ schedule →
      ¬F1 stage ∧ ¬F2 stage ∧ ¬F3 stage ∧ ¬F4 stage) → Germ

/-- Build the exact one-source profile.  `germOfClear` is invoked only from
the generic runner's exhaustive no-event branch. -/
def profile {Stage : Type uStage}
    (stages : Core.OrderedCollection Stage)
    (F1 : Stage → Prop) (f1Decidable : ∀ stage, Decidable (F1 stage))
    (F1Data : Type uF1) (f1Data : ∀ stage, F1 stage → F1Data)
    (later : LaterSemantics.{uStage, uF2, uF3, uF4, uGerm} Stage F1) :
    Core.FiniteFirstFailure.Profile Unit Stage where
  corridors := inferInstance
  stages := fun _ => stages
  F1 := fun _ stage => F1 stage
  F2 := fun _ stage => later.F2 stage
  F3 := fun _ stage => later.F3 stage
  F4 := fun _ stage => later.F4 stage
  f1Decidable := fun _ stage => f1Decidable stage
  f2Decidable := fun _ stage => later.f2Decidable stage
  f3Decidable := fun _ stage => later.f3Decidable stage
  f4Decidable := fun _ stage => later.f4Decidable stage
  F1Data := F1Data
  F2Data := later.F2Data
  F3Data := later.F3Data
  F4Data := later.F4Data
  f1Data := fun _ stage proof => f1Data stage proof
  f2Data := fun _ stage proof => later.f2Data stage proof
  f3Data := fun _ stage proof => later.f3Data stage proof
  f4Data := fun _ stage proof => later.f4Data stage proof
  Germ := fun _ => later.Germ
  germOfClear := fun _ clear => later.germOfClear stages.values
    (fun stage member =>
      ⟨(clear stage member).1,
        (clear stage member).2.1,
        (clear stage member).2.2.1,
        (clear stage member).2.2.2⟩)

end StructuralExhaustion.Core.FinitePrioritizedContinuation
