import Hypostructure.Core.Finite.ScheduleEvents
import Hypostructure.Core.Routing

/-!
# Schedule-event route bridge

This module owns the generic handoff from a schedule-event hit branch to a
registered framework route.  Core selects the exact hit witness from the
event-hit residual and packages the item, membership, runner output, and event
proof into a route seed.  Applications provide only the downstream target
executor and the target input read from that Core-owned seed.
-/

namespace Hypostructure.Core.Finite.ScheduleEventRoute

open Hypostructure.Core
open Hypostructure.Core.Residual

universe uPrevious uItem uOutput uInput uOutcome uTrace

/-- Core-owned seed for downstream routing from a schedule-event hit branch. -/
structure Seed {Previous : Type uPrevious} {focus : Focus.Profile Previous}
    {contract :
      ScheduleEvents.FocusedContract.{uPrevious + 1, uItem, uOutput} focus}
    (stage : contract.Stage) where
  active : contract.hitFocus.Active stage
  item : contract.Item
  member : item ∈ (contract.schedule.read stage.previous active.parent).values
  output : contract.Output stage.previous active.parent item
  output_exact :
    output = (contract.runner.read stage.previous active.parent) item
  event : contract.event stage.previous active.parent item output

namespace Seed

variable {Previous : Type uPrevious} {focus : Focus.Profile Previous}
variable
  {contract :
    ScheduleEvents.FocusedContract.{uPrevious + 1, uItem, uOutput} focus}

/-- Build the route seed from the exact active event-hit branch. -/
noncomputable def ofActive (stage : contract.Stage)
    (active : contract.hitFocus.Active stage) :
    Seed stage := by
  let hit := contract.hitQuery.read stage active
  let item := Classical.choose hit
  let rest := Classical.choose_spec hit
  let member := rest.1
  let event := rest.2
  exact
    { active := active
      item := item
      member := member
      output := (contract.runner.read stage.previous active.parent) item
      output_exact := rfl
      event := event }

@[simp] theorem ofActive_output_exact (stage : contract.Stage)
    (active : contract.hitFocus.Active stage) :
    (ofActive stage active).output =
      (contract.runner.read stage.previous active.parent)
        (ofActive stage active).item :=
  (ofActive stage active).output_exact

end Seed

variable {Previous : Type uPrevious} {focus : Focus.Profile Previous}
variable
  {eventContract :
    ScheduleEvents.FocusedContract.{uPrevious + 1, uItem, uOutput} focus}

/-- Framework routing profile enabled exactly on the event-hit focus. -/
noncomputable def profile :
    (target :
      Execution.Spec.{_, uInput, uOutcome, uTrace} eventContract.Stage) ->
    (executor : Execution.Capability target) ->
    (targetInput :
      (stage : eventContract.Stage) ->
        Seed stage -> target.Input stage) ->
    Routing.Profile.{_, uInput, uOutcome, uTrace, _, 0}
      eventContract.Stage :=
  fun target executor targetInput =>
  Routing.Profile.ofFocus
    eventContract.hitFocus
    target
    executor
    Seed
    (fun stage active => Seed.ofActive stage active)
    targetInput

/-- Register this schedule-event hit route under a stable edge identity. -/
noncomputable def transition (edge : Routing.Edge) :
    (target :
      Execution.Spec.{_, uInput, uOutcome, uTrace} eventContract.Stage) ->
    (executor : Execution.Capability target) ->
    (targetInput :
      (stage : eventContract.Stage) ->
        Seed stage -> target.Input stage) ->
    Routing.Transition.{_, uInput, uOutcome, uTrace, _, 0}
      edge eventContract.Stage :=
  fun target executor targetInput =>
    Routing.Transition.register edge
      (profile target executor targetInput)

/-- Execute the registered route from the literal schedule-event stage. -/
noncomputable def advance (edge : Routing.Edge)
    (target :
      Execution.Spec.{_, uInput, uOutcome, uTrace} eventContract.Stage)
    (executor : Execution.Capability target)
    (targetInput :
      (stage : eventContract.Stage) ->
        Seed stage -> target.Input stage)
    (stage : eventContract.Stage) :
    Routing.Stage (transition edge target executor targetInput) :=
  Routing.advance (transition edge target executor targetInput) stage

@[simp] theorem advance_previous (edge : Routing.Edge)
    (target :
      Execution.Spec.{_, uInput, uOutcome, uTrace} eventContract.Stage)
    (executor : Execution.Capability target)
    (targetInput :
      (stage : eventContract.Stage) ->
        Seed stage -> target.Input stage)
    (stage : eventContract.Stage) :
    (advance edge target executor targetInput stage).previous = stage :=
  Routing.advance_previous (transition edge target executor targetInput) stage

end Hypostructure.Core.Finite.ScheduleEventRoute
