import StructuralExhaustion.CT12.RefinedLedgerCompletion

namespace StructuralExhaustion.Examples.CT12RefinedLedgerCompletion

open StructuralExhaustion

abbrev problem : Core.Problem where
  Ambient := Unit
  Baseline := fun _ => True
  rank := fun _ => 0
  BranchState := fun _ => Unit

def context : Core.BranchContext problem := ⟨(), trivial, ()⟩

def profile : CT12.RefinedLedgerCompletion.Profile Bool (Fin 2) where
  Candidate := fun _ => Unit
  demands := Core.Enumeration.bool
  finiteCandidates := fun _ => inferInstance
  carrierSupport := fun demand _ => if demand then {0} else {1}
  demandSupport := fun demand => if demand then {0} else {1}
  carrierSupport_subset := fun _demand _candidate => Finset.Subset.rfl

def stage := profile.verifiedStage context

example : (profile.run context).terminal = .exhausted := stage.terminal
example : (profile.run context).iterations = profile.demands.card :=
  stage.iterationsExact
example : Nonempty profile.FullChoice ∨ profile.FullObstruction :=
  stage.alternative
example : Nonempty profile.FullChoice ∨
    ∃ selected, selected.Sublist profile.fullSchedule ∧
      profile.MinimalOverlapObstruction selected :=
  stage.minimalAlternative
example : profile.overlapSupport [false] ⊆
    profile.overlapSupport profile.fullSchedule := by
  apply profile.overlapSupport_mono
  simp [Core.FiniteRefinedLedger.Profile.fullSchedule, profile,
    Core.Enumeration.bool]

end StructuralExhaustion.Examples.CT12RefinedLedgerCompletion
