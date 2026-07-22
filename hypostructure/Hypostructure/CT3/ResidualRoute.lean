import Hypostructure.CT3.ScheduleWitness
import Hypostructure.Core.Routing

/-!
# CT3 residual routing bridge

This module owns the generic handoff from a scheduled CT3 residual branch to a
registered framework route.  CT3 selects the exact first residual item,
terminal, and witness from the residual ledger; applications only provide the
target execution contract and the target input built from that CT3-owned seed.
-/

namespace Hypostructure.CT3.ResidualRoute

open Hypostructure.Core
open Hypostructure.Core.Residual

universe uPrevious uItem uGood uResidual uInput uOutcome uTrace

/-- CT3-owned seed for downstream residual routing.  It packages the selected
residual focus proof, exact first residual hit, terminal, and domain witness. -/
structure Seed {Previous : Type uPrevious} {focus : Focus.Profile Previous}
    {schedule : Schedule.FocusedContract.{uPrevious + 1, uItem} focus}
    (evidence :
      (previous : Previous) -> (active : focus.Active previous) ->
        ScheduleWitness.EvidenceContract.{uItem, uGood, uResidual}
          (schedule.scheduleAt previous active))
    (stage : schedule.Stage) where
  active : schedule.residualFocus.Active stage
  hit : schedule.FirstResidual stage.previous active.parent
  terminal :
    (schedule.scheduleAt stage.previous active.parent).ResidualTerminal
      hit.value
  witness :
    (evidence stage.previous active.parent).ResidualWitness hit.value

namespace Seed

variable {Previous : Type uPrevious} {focus : Focus.Profile Previous}
variable {schedule : Schedule.FocusedContract.{uPrevious + 1, uItem} focus}
variable
  (evidence :
    (previous : Previous) -> (active : focus.Active previous) ->
      ScheduleWitness.EvidenceContract.{uItem, uGood, uResidual}
        (schedule.scheduleAt previous active))

/-- Build the CT3 residual route seed from the exact active residual branch. -/
noncomputable def ofActive (stage : schedule.Stage)
    (active : schedule.residualFocus.Active stage) :
    Seed evidence stage := by
  let hit := schedule.residualQuery.read stage active
  exact
    { active := active
      hit := hit
      terminal := hit.sound
      witness :=
        (evidence stage.previous active.parent).residualWitnessAtFirstHit
          hit }

@[simp] theorem ofActive_hit (stage : schedule.Stage)
    (active : schedule.residualFocus.Active stage) :
    (ofActive evidence stage active).hit =
      schedule.residualQuery.read stage active :=
  rfl

end Seed

/-- Contract for routing a CT3 residual branch into a downstream target
executor.  The downstream target result is produced by Core routing, never by
the application. -/
structure Contract {Previous : Type uPrevious}
    {focus : Focus.Profile Previous}
    (schedule : Schedule.FocusedContract.{uPrevious + 1, uItem} focus) where
  evidence :
    (previous : Previous) -> (active : focus.Active previous) ->
      ScheduleWitness.EvidenceContract.{uItem, uGood, uResidual}
        (schedule.scheduleAt previous active)
  target :
    Execution.Spec.{_, uInput, uOutcome, uTrace} schedule.Stage
  executor : Execution.Capability target
  targetInput :
    (stage : schedule.Stage) ->
      Seed evidence stage -> target.Input stage

namespace Contract

variable {Previous : Type uPrevious} {focus : Focus.Profile Previous}
variable {schedule : Schedule.FocusedContract.{uPrevious + 1, uItem} focus}
variable (contract : ResidualRoute.Contract schedule)

/-- Framework routing profile enabled exactly on the CT3 residual focus. -/
noncomputable def profile :
    Routing.Profile.{_, uInput, uOutcome, uTrace, _, 0}
      schedule.Stage :=
  Routing.Profile.ofFocus
    schedule.residualFocus
    contract.target
    contract.executor
    (Seed contract.evidence)
    (fun stage active => Seed.ofActive contract.evidence stage active)
    contract.targetInput

/-- Register this CT3 residual route under a stable edge identity. -/
noncomputable def transition (edge : Routing.Edge) :
    Routing.Transition.{_, uInput, uOutcome, uTrace, _, 0}
      edge schedule.Stage :=
  Routing.Transition.register edge contract.profile

/-- Execute the registered CT3 residual route from the literal CT3 schedule
stage. -/
noncomputable def advance (edge : Routing.Edge)
    (stage : schedule.Stage) :
    Routing.Stage (contract.transition edge) :=
  Routing.advance (contract.transition edge) stage

@[simp] theorem advance_previous (edge : Routing.Edge)
    (stage : schedule.Stage) :
    (contract.advance edge stage).previous = stage :=
  Routing.advance_previous (contract.transition edge) stage

/-- Execute CT3 schedule classification from the predecessor, then route the
framework-selected first residual branch.  This is the high-level CT3-owned
composition used when downstream applications should not manually thread the
intermediate schedule stage. -/
noncomputable def advanceClassified (edge : Routing.Edge)
    (previous : Previous) :
    Routing.Stage (contract.transition edge) :=
  contract.advance edge (schedule.runStage previous)

@[simp] theorem advanceClassified_previous (edge : Routing.Edge)
    (previous : Previous) :
    (contract.advanceClassified edge previous).previous =
      schedule.runStage previous :=
  contract.advance_previous edge (schedule.runStage previous)

@[simp] theorem advanceClassified_source_previous (edge : Routing.Edge)
    (previous : Previous) :
    (contract.advanceClassified edge previous).previous.previous = previous := by
  rw [contract.advanceClassified_previous edge previous]
  exact schedule.runStage_previous previous

end Contract

end Hypostructure.CT3.ResidualRoute
