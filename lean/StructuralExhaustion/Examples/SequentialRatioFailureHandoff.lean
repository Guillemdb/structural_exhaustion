import StructuralExhaustion.Examples.FiniteSequentialFiltration
import StructuralExhaustion.Routes.SequentialRatioFailureHandoff

namespace StructuralExhaustion.Examples.SequentialRatioFailureHandoff

open StructuralExhaustion
open StructuralExhaustion.Core.FiniteSequentialFiltration
open StructuralExhaustion.Examples.FiniteSequentialFiltration

abbrev problem : Core.Problem where
  Ambient := Unit
  Baseline := fun _ => True
  rank := fun _ => 0
  BranchState := fun _ => Unit

def context : Core.BranchContext problem :=
  ⟨(), trivial, ()⟩

def source : Routes.SequentialRatioFailureHandoff.Source context failingProfile where
  failure := failingFailure
  run_eq := failing_result

def residual : Routes.SequentialRatioFailureHandoff.Residual context failingProfile :=
  Routes.SequentialRatioFailureHandoff.handoff source

example : residual.source = source := rfl

example : residual.index = 1 := by
  native_decide

example : residual.beforeStates.length = 4 := by
  native_decide

example : residual.afterStates.length = 3 := by
  native_decide

example : Fails residual.beforeStates residual.barrier :=
  Routes.SequentialRatioFailureHandoff.routed_fails source

example : List.Sublist residual.afterStates residual.beforeStates :=
  Routes.SequentialRatioFailureHandoff.routed_after_sublist_before source

example : failingProfile.run = Outcome.firstFailure residual.source.failure :=
  Routes.SequentialRatioFailureHandoff.routed_run_eq source

example : Routes.SequentialRatioFailureHandoff.handoffId =
    "finite-sequential-ratio-failure->arithmetic-handoff" :=
  rfl

end StructuralExhaustion.Examples.SequentialRatioFailureHandoff
