import Hypostructure.CT1.Automation

/-!
# PDE fast-track target compactification

Target compactification is the PDE-facing CT1 adapter for a residual-owned
finite family of compactified target representatives.  The PDE layer supplies
only the finite schedule and primitive realization predicate; CT1 owns the
scan, terminal, ledger extension, trace, and work accounting.
-/

namespace Hypostructure.PDE.FastTrack.TargetCompactification

universe uPrevious uCandidate

/-- Minimal PDE registration for a compactified target family over the exact
incoming residual. -/
structure Profile (Previous : Type uPrevious) where
  Candidate : Previous -> Type uCandidate
  Realizes : (previous : Previous) -> Candidate previous -> Prop
  schedule : Hypostructure.Core.Residual.Query Previous fun previous =>
    Hypostructure.Core.Finite.Enumeration (Candidate previous)
  realizesDecidable : (previous : Previous) -> (candidate : Candidate previous) ->
    Decidable (Realizes previous candidate)
  inputSize : Previous -> Nat
  workCoefficient : Nat
  workDegree : Nat
  workBound : forall previous,
    _root_.Hypostructure.CT1.searchCheckBound
      ({ Candidate := Candidate, Realizes := Realizes } :
        _root_.Hypostructure.CT1.Spec Previous) schedule previous <=
        workCoefficient * (inputSize previous + 1) ^ workDegree

namespace Profile

/-- Shared CT1 spec induced by the compactified target registration. -/
def spec (profile : Profile Previous) :
    _root_.Hypostructure.CT1.Spec Previous where
  Candidate := profile.Candidate
  Realizes := profile.Realizes

/-- Shared CT1 capability induced by the compactified target registration. -/
def capability (profile : Profile Previous) :
    _root_.Hypostructure.CT1.Capability profile.spec where
  schedule := profile.schedule
  realizesDecidable := profile.realizesDecidable
  inputSize := profile.inputSize
  workCoefficient := profile.workCoefficient
  workDegree := profile.workDegree
  workBound := profile.workBound

/-- Execute target compactification through CT1. -/
def run (profile : Profile Previous) (previous : Previous) :
    _root_.Hypostructure.CT1.ExecutionResult profile.spec profile.capability :=
  _root_.Hypostructure.CT1.run profile.spec profile.capability previous

@[simp] theorem run_previous (profile : Profile Previous) (previous : Previous) :
    (profile.run previous).stage.previous = previous :=
  _root_.Hypostructure.CT1.run_previous profile.spec profile.capability previous

/-- The target-compactification executor is exactly CT1 soundness. -/
theorem run_verified (profile : Profile Previous) (previous : Previous) :
    _root_.Hypostructure.CT1.OutcomeClaim profile.spec profile.capability
      previous (profile.run previous).terminal :=
  _root_.Hypostructure.CT1.run_verified profile.spec profile.capability previous

end Profile

end Hypostructure.PDE.FastTrack.TargetCompactification
