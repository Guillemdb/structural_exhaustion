import Hypostructure.Core.Finite.ScaleRoute
import Hypostructure.Core.Finite.ScheduleEventRoute
import Hypostructure.Core.Finite.ScheduleEvents
import Hypostructure.Core.Routing
import Hypostructure.CT3.Schedule

/-!
# Cold-branch automation fixtures

Neutral fixtures for the Core/CT3 automation patterns behind the cold branch:
schedule-wide event splits, bounded-vs-long scale routing, and CT3 terminal
classification.
-/

namespace Hypostructure.Fixtures.ColdBranchAutomation

open Hypostructure.Core
open Hypostructure.Core.Finite
open Hypostructure.Core.Residual

def items : Enumeration Nat :=
  { values := [0, 1, 2]
    nodup := by decide
    decEq := inferInstance }

def eventContract : ScheduleEvents.Contract Nat where
  schedule := items
  Output := fun _ => Nat
  run := fun item => item + 1

def isThree (item : Nat) (output : Nat) : Prop :=
  item = 2 ∧ output = 3

def isThreeDecidable (item : Nat) :
    Decidable (isThree item (eventContract.run item)) := by
  unfold isThree
  infer_instance

theorem event_split :
    eventContract.ExistsEvent isThree ∨
      eventContract.NoEvent isThree :=
  eventContract.firstHit_or_noEvent isThree isThreeDecidable

abbrev focusedEventFocus : Focus.Profile Unit :=
  Focus.always Unit

def focusedScheduleQuery :
    Focus.ActiveQuery focusedEventFocus fun _previous _active =>
      Enumeration Nat :=
  Focus.ActiveQuery.ofFunction fun _previous _active => items

def focusedRunnerQuery :
    Focus.ActiveQuery focusedEventFocus fun _previous _active =>
      (item : Nat) -> Nat :=
  Focus.ActiveQuery.ofFunction fun _previous _active item => item + 1

def focusedEventContract :
    ScheduleEvents.FocusedContract.{1, 0, 0} focusedEventFocus where
  Item := Nat
  schedule := focusedScheduleQuery
  Output := fun _previous _active _item => Nat
  runner := focusedRunnerQuery
  event := fun _previous _active item output => isThree item output
  eventDecidable := fun _previous _active item => isThreeDecidable item

def focusedEventStage : focusedEventContract.Stage :=
  focusedEventContract.runStage ()

theorem focusedEvent_preserves_previous :
    focusedEventStage.previous = () :=
  focusedEventContract.runStage_previous ()

def focusedHitStage :
    focusedEventContract.hitFocus.Active focusedEventStage := by
  refine ⟨trivial, ?_⟩
  unfold focusedEventContract focusedEventStage
  refine ⟨?_, rfl⟩
  refine ⟨2, ?_, ?_⟩
  · decide
  · rw [focusedEventContract.runStage_previous ()]
    simp [ScheduleEvents.FocusedContract.finiteContract,
      focusedRunnerQuery, isThree]

theorem focusedHitEntry :
    ∃ item ∈ items.values, isThree item (item + 1) :=
  (@ScheduleEvents.FocusedContract.hitQuery.{1, 0, 0, 0, 0} Unit focusedEventFocus
    focusedEventContract).read focusedEventStage focusedHitStage

def eventRouteTarget :
    Execution.Spec focusedEventContract.Stage where
  Input := fun _stage => Nat
  Outcome := fun _stage _input => Unit
  Trace := fun _stage _input _outcome => Unit
  Sound := fun _stage _input _outcome _trace => True
  Exhaustive := fun _stage _input _outcome => True

def eventRouteExecutor : Execution.Capability eventRouteTarget where
  reference := fun _stage _input => ⟨⟨(), ()⟩, 1⟩
  sound := by
    intro _stage _input
    trivial
  exhaustive := by
    intro _stage _input
    trivial
  work := PolynomialCheckBudget.constant (fun _ => 1) 1
  checks_eq := by
    intro _stage _input
    rfl

def eventRouteInput (stage : focusedEventContract.Stage)
    (seed : ScheduleEventRoute.Seed stage) : Nat :=
  seed.item

def eventRouteEdge : Routing.Edge :=
  ⟨.ct6, .ct3, "neutral-schedule-event-hit-route-fixture"⟩

noncomputable def eventRouted :
    Routing.Stage
      (ScheduleEventRoute.transition eventRouteEdge eventRouteTarget
        eventRouteExecutor eventRouteInput) :=
  ScheduleEventRoute.advance eventRouteEdge eventRouteTarget
    eventRouteExecutor eventRouteInput focusedEventStage

theorem event_route_preserves_stage :
    eventRouted.previous = focusedEventStage :=
  ScheduleEventRoute.advance_previous eventRouteEdge eventRouteTarget
    eventRouteExecutor eventRouteInput focusedEventStage

theorem event_route_profile_enabled :
    ∃ seed,
      (ScheduleEventRoute.profile eventRouteTarget eventRouteExecutor
        eventRouteInput).discover focusedEventStage =
        Routing.Discovery.enabled seed := by
  refine ⟨ScheduleEventRoute.Seed.ofActive focusedEventStage focusedHitStage, ?_⟩
  change
    ((Routing.Profile.ofFocus
      focusedEventContract.hitFocus
      eventRouteTarget
      eventRouteExecutor
      ScheduleEventRoute.Seed
      (fun stage active => ScheduleEventRoute.Seed.ofActive stage active)
      eventRouteInput).discover focusedEventStage) =
      Routing.Discovery.enabled
        (ScheduleEventRoute.Seed.ofActive focusedEventStage focusedHitStage)
  exact Routing.Profile.ofFocus_discover_active
    focusedEventContract.hitFocus
    eventRouteTarget
    eventRouteExecutor
    ScheduleEventRoute.Seed
    (fun stage active => ScheduleEventRoute.Seed.ofActive stage active)
    eventRouteInput
    focusedEventStage focusedHitStage

def noHitEventContract :
    ScheduleEvents.FocusedContract.{1, 0, 0} focusedEventFocus where
  Item := Nat
  schedule := focusedScheduleQuery
  Output := fun _previous _active _item => Nat
  runner := focusedRunnerQuery
  event := fun _previous _active item output => item = 5 ∧ output = 6
  eventDecidable := fun _previous _active item => by
    change Decidable (item = 5 ∧ item + 1 = 6)
    infer_instance

def noHitEventStage : noHitEventContract.Stage :=
  noHitEventContract.runStage ()

def noHitEventActive :
    noHitEventContract.noEventFocus.Active noHitEventStage := by
  refine ⟨trivial, ?_⟩
  unfold noHitEventContract noHitEventStage
  refine ⟨?_, rfl⟩
  intro existsHit
  rcases existsHit with ⟨item, member, event⟩
  have member' : item ∈ items.values := by
    rw [noHitEventContract.runStage_previous ()] at member
    simpa [ScheduleEvents.FocusedContract.finiteContract,
      focusedScheduleQuery] using member
  have item_cases : item = 0 ∨ item = 1 ∨ item = 2 := by
    simpa [items] using member'
  rcases item_cases with rfl | rfl | rfl <;> simp at event

theorem noHit_pointwise_absent :
    ∀ item ∈ items.values, Not (item = 5 ∧ item + 1 = 6) :=
  (@ScheduleEvents.FocusedContract.pointwiseAbsentQuery.{1, 0, 0, 0, 0} Unit
    focusedEventFocus noHitEventContract).read noHitEventStage
      noHitEventActive

theorem noHit_pointwise_absent_output :
    ∀ item, (member : item ∈ items.values) ->
      (((@ScheduleEvents.FocusedContract.pointwiseAbsentOutputQuery.{1, 0, 0, 0, 0}
        Unit focusedEventFocus noHitEventContract).read noHitEventStage
          noHitEventActive item member).1 = item + 1) := by
  intro item member
  rfl

def noHitRemaining (_item _output : Nat) : Prop :=
  True

theorem noHit_pointwise_remaining :
    ∀ item, item ∈ items.values ->
      noHitRemaining item (item + 1) :=
  (@ScheduleEvents.FocusedContract.pointwiseRemainingQuery.{1, 0, 0, 0, 0}
      Unit focusedEventFocus noHitEventContract
      (fun _previous _active item output => noHitRemaining item output)
      (fun _previous _active item _output _absent => by
        unfold noHitRemaining
        trivial)).read noHitEventStage noHitEventActive

def scaleContract : ScaleRoute.Contract Nat where
  supportSize := fun item => item
  scale := fun _ => 3

theorem scale_bounded_if_not_long (item : Nat)
    (notLong : Not (scaleContract.Long item)) :
    scaleContract.Bounded item :=
  scaleContract.bounded_of_long_impossible item notLong

def focusedScaleFocus : Focus.Profile Unit :=
  Focus.always Unit

def boundedScaleContract :
    ScaleRoute.FocusedContract.{1, 0} focusedScaleFocus where
  Item := Nat
  item := Focus.ActiveQuery.ofFunction fun _previous _active => 2
  supportSize := Focus.ActiveQuery.ofFunction fun _previous _active => 2
  scale := Focus.ActiveQuery.ofFunction fun _previous _active => 3

def boundedScaleStage : boundedScaleContract.Stage :=
  boundedScaleContract.runStage ()

def boundedScaleActive :
    boundedScaleContract.boundedFocus.Active boundedScaleStage := by
  refine ⟨trivial, ?_⟩
  unfold boundedScaleContract boundedScaleStage
  refine ⟨?_, rfl⟩
  change 2 <= 3
  decide

theorem boundedScale_read :
    boundedScaleContract.Bounded boundedScaleStage.previous trivial :=
  (@ScaleRoute.FocusedContract.boundedQuery.{1, 0} Unit
    focusedScaleFocus boundedScaleContract).read boundedScaleStage
      boundedScaleActive

def longScaleContract :
    ScaleRoute.FocusedContract.{1, 0} focusedScaleFocus where
  Item := Nat
  item := Focus.ActiveQuery.ofFunction fun _previous _active => 5
  supportSize := Focus.ActiveQuery.ofFunction fun _previous _active => 5
  scale := Focus.ActiveQuery.ofFunction fun _previous _active => 3

def longScaleStage : longScaleContract.Stage :=
  longScaleContract.runStage ()

def longScaleActive :
    longScaleContract.longFocus.Active longScaleStage := by
  refine ⟨trivial, ?_⟩
  unfold longScaleContract longScaleStage
  refine ⟨?_, rfl⟩
  change 3 < 5
  decide

theorem longScale_read :
    longScaleContract.Long longScaleStage.previous trivial :=
  (@ScaleRoute.FocusedContract.longQuery.{1, 0} Unit
    focusedScaleFocus longScaleContract).read longScaleStage longScaleActive

theorem focusedScale_bounded_of_long_impossible
    (notLong : Not (boundedScaleContract.Long () trivial)) :
    boundedScaleContract.Bounded () trivial :=
  boundedScaleContract.bounded_of_long_impossible () trivial notLong

def scheduleScaleContract :
    ScaleRoute.FocusedScheduleContract.{1, 0} focusedScaleFocus where
  Item := Nat
  schedule := focusedScheduleQuery
  supportSize := fun _previous _active item => item
  scale := fun _previous _active _item => 3

def scheduleScaleStage : scheduleScaleContract.Stage :=
  scheduleScaleContract.runStage ()

def scheduleScaleAllBoundedActive :
    scheduleScaleContract.allBoundedFocus.Active scheduleScaleStage := by
  refine ⟨trivial, ?_⟩
  unfold scheduleScaleContract scheduleScaleStage
  refine ⟨?_, rfl⟩
  intro item member
  rw [scheduleScaleContract.runStage_previous ()] at member
  have item_cases : item = 0 ∨ item = 1 ∨ item = 2 := by
    simpa [focusedScheduleQuery, items] using member
  rcases item_cases with rfl | rfl | rfl
  · change 0 <= 3
    decide
  · change 1 <= 3
    decide
  · change 2 <= 3
    decide

theorem scheduleScale_allBounded :
    scheduleScaleContract.AllBounded scheduleScaleStage.previous trivial :=
  (@ScaleRoute.FocusedScheduleContract.allBoundedQuery.{1, 0} Unit
    focusedScaleFocus scheduleScaleContract).read scheduleScaleStage
      scheduleScaleAllBoundedActive

def scheduleLongScaleContract :
    ScaleRoute.FocusedScheduleContract.{1, 0} focusedScaleFocus where
  Item := Nat
  schedule :=
    Focus.ActiveQuery.ofFunction fun _previous _active =>
      ({ values := [0, 5]
         nodup := by decide
         decEq := inferInstance } : Enumeration Nat)
  supportSize := fun _previous _active item => item
  scale := fun _previous _active _item => 3

def scheduleLongScaleStage : scheduleLongScaleContract.Stage :=
  scheduleLongScaleContract.runStage ()

def scheduleLongScaleActive :
    scheduleLongScaleContract.longFocus.Active scheduleLongScaleStage := by
  refine ⟨trivial, ?_⟩
  unfold scheduleLongScaleContract scheduleLongScaleStage
  refine ⟨?_, rfl⟩
  refine ⟨5, ?_, ?_⟩
  · decide
  · change 3 < 5
    decide

theorem scheduleLongScale_hasLong :
    scheduleLongScaleContract.AnyLong scheduleLongScaleStage.previous trivial :=
  (@ScaleRoute.FocusedScheduleContract.longQuery.{1, 0} Unit
    focusedScaleFocus scheduleLongScaleContract).read scheduleLongScaleStage
      scheduleLongScaleActive

def ct3Contract : Hypostructure.CT3.Schedule.Contract Nat where
  items := items
  terminal
    | 0 => .compression
    | 1 => .knownRow
    | _ => .novelRow

theorem ct3_classifies :
    ct3Contract.AllGood ∨ ct3Contract.HasResidual :=
  ct3Contract.allGood_or_hasResidual

#print axioms event_split
#print axioms focusedHitEntry
#print axioms event_route_preserves_stage
#print axioms event_route_profile_enabled
#print axioms noHit_pointwise_absent
#print axioms noHit_pointwise_absent_output
#print axioms noHit_pointwise_remaining
#print axioms scale_bounded_if_not_long
#print axioms boundedScale_read
#print axioms longScale_read
#print axioms focusedScale_bounded_of_long_impossible
#print axioms scheduleScale_allBounded
#print axioms scheduleLongScale_hasLong
#print axioms ct3_classifies

end Hypostructure.Fixtures.ColdBranchAutomation
