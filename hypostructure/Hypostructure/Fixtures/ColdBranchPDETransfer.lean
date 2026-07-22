import Hypostructure.Core.Finite.Flatten
import Hypostructure.Core.Finite.Partition
import Hypostructure.Core.Finite.ScaleRoute
import Hypostructure.Core.Finite.ScheduleEventRoute
import Hypostructure.Core.Finite.ScheduleEvents
import Hypostructure.Core.Finite.SelectedSchedule
import Hypostructure.Core.Execution
import Hypostructure.Core.Routing
import Hypostructure.Core.Response.SameInterface
import Hypostructure.CT3.ResidualRoute
import Hypostructure.CT3.SameInterface
import Hypostructure.CT3.ScheduleWitness
import Hypostructure.PDE.CT3
import Hypostructure.PDE.CT6
import Hypostructure.PDE.Model

/-!
# PDE transfer fixture for cold-branch Core capabilities

This fixture uses PDE-shaped names -- windows, shells, atoms, local packets,
and response packages -- but instantiates only Core/CT contracts.  Its purpose
is to keep the cold-branch automation APIs domain-neutral: the same machinery
used by graph cold branches is available to PDE reductions through residual
queries, finite schedules, CT-owned routing, and ledger retrieval.
-/

namespace Hypostructure.Fixtures.ColdBranchPDETransfer

open Hypostructure.Core
open Hypostructure.Core.Finite
open Hypostructure.Core.Residual

inductive Window where
  | near
  | far
  | tail
deriving DecidableEq

inductive Shell where
  | low
  | high
deriving DecidableEq

structure LocalAtom where
  window : Window
  shell : Shell
deriving DecidableEq

structure PDEPacket where
  amplitude : Nat
  scale : Nat
deriving DecidableEq

abbrev pdeProblem : Core.Problem where
  Ambient := Unit
  Baseline := fun _state => True
  BranchState := fun _state => Unit

def pdeAtlas : PDE.LocalAtlas pdeProblem where
  Point := Unit
  Window := Unit
  contains := fun _point _window => True
  nested := fun _small _large => True
  nested_refl := fun _window => trivial
  nested_trans := fun _first _second => trivial
  core := id
  core_nested := fun _window => trivial
  LocalObject := fun _window => Unit
  restrict := fun _state _window => ()
  restrictLocal := fun _nested object => object
  restrict_refl := fun _window _object => rfl
  restrict_trans := fun _smallLarge _largeWork _object => rfl
  restrict_global := by
    intro state small large nested
    rfl

def pdeEquation : PDE.RepresentedEquation pdeProblem pdeAtlas where
  EquationData := fun _window _object => Unit
  satisfies := fun _data => True
  restrictEquation := fun _nested _object data => data
  restrict_satisfies := fun _nested _object _data valid => valid

abbrev pdeModel : PDE.LocalModel where
  problem := pdeProblem
  atlas := pdeAtlas
  equation := pdeEquation

def pdeState :
    Focus.ActiveQuery focus fun _previous _active => pdeModel.problem.Ambient :=
  Focus.ActiveQuery.ofFunction fun _previous _active => ()

abbrev focus : Focus.Profile Unit :=
  Focus.always Unit

def windowSchedule : Enumeration Window :=
  Enumeration.ofNodupList [Window.near, Window.far, Window.tail] (by decide)

def selectedWindows :
    Focus.ActiveQuery focus fun _previous _active => Enumeration Window :=
  Focus.ActiveQuery.ofFunction fun _previous _active => windowSchedule

def selectedContract : SelectedSchedule.Contract focus where
  Item := Window
  selected := selectedWindows

def selectedStage : selectedContract.Stage :=
  selectedContract.run ()

theorem selected_card_from_ledger :
    selectedContract.latestCard.read selectedStage trivial = 3 :=
  rfl

theorem selected_card_exact_from_ledger :
    selectedContract.latestCard.read selectedStage trivial =
      (selectedWindows.read () trivial).card :=
  selectedContract.latestCardExact.read selectedStage trivial

theorem selected_attached_card_from_ledger :
    (selectedContract.latestAttached.read selectedStage trivial).card =
      windowSchedule.card := by
  have card :=
    selectedContract.latestAttachedCardExact.read selectedStage trivial
  have schedule_eq :
      (selectedWindows.read selectedStage.previous trivial).card =
        windowSchedule.card := by
    simp [selectedStage, selectedContract, selectedWindows]
  exact card.trans schedule_eq

theorem selected_attached_windows_from_ledger :
    ∀ entry ∈ (selectedContract.latestAttached.read selectedStage
        trivial).values,
      entry.1 ∈ windowSchedule.values := by
  intro entry _member
  exact entry.2

def nearWindow (window : Window) : Prop :=
  window = Window.near

def nearWindowDecidable (window : Window) : Decidable (nearWindow window) := by
  unfold nearWindow
  infer_instance

def partitionContract : Partition.FocusedContract.{1, 0} focus where
  Item := Window
  schedule := selectedWindows
  predicate := fun _previous _active window => nearWindow window
  decidePredicate := fun _previous _active => nearWindowDecidable

def partitionStage : partitionContract.Stage :=
  partitionContract.runStage ()

theorem partition_card_exact :
    (partitionContract.latestAccepted.read partitionStage trivial).card +
        (partitionContract.latestRejected.read partitionStage trivial).card =
      windowSchedule.card := by
  have card := partitionContract.latestCardPartition.read partitionStage trivial
  have schedule_eq :
      ((partitionContract.schedule.preserve).read partitionStage trivial).card =
        windowSchedule.card := by
    simp [partitionStage, partitionContract, selectedWindows]
  exact card.trans schedule_eq

def atomsForWindow (_window : Window) : Enumeration Shell :=
  Enumeration.ofNodupList [Shell.low, Shell.high] (by decide)

def atomFamily : DependentEnumeration Window fun _window => Shell where
  indices := windowSchedule
  fibres := atomsForWindow

def atomFamilyQuery :
    Focus.ActiveQuery focus fun _previous _active =>
      DependentEnumeration Window fun _window => Shell :=
  Focus.ActiveQuery.ofFunction fun _previous _active => atomFamily

def flattenContract : Flatten.FocusedContract.{1, 0, 0} focus where
  Index := Window
  Fibre := fun _window => Shell
  schedule := atomFamilyQuery

def flattenStage : flattenContract.Stage :=
  flattenContract.runStage ()

def constantShellFibres :
    Focus.ActiveQuery flattenContract.successor fun stage active =>
      ∀ window ∈ ((flattenContract.schedule.preserve).read stage
          active).indices.values,
        (((flattenContract.schedule.preserve).read stage
          active).fibres window).card = 2 :=
  Focus.ActiveQuery.ofFunction fun _stage _active window _member => by
    cases window <;> rfl

theorem flattened_atom_count :
    (flattenContract.latestFlattened.read flattenStage trivial).card =
      2 * windowSchedule.card := by
  have card :=
    (flattenContract.latestCardEqContributionMul 2
      constantShellFibres).read flattenStage trivial
  have rhs_eq :
      2 *
          ((flattenContract.schedule.preserve).read flattenStage
            trivial).indices.card =
        2 * windowSchedule.card := by
    simp [flattenStage, flattenContract, atomFamilyQuery, atomFamily]
  exact card.trans rhs_eq

def packetRunner (window : Window) : PDEPacket :=
  match window with
  | .near => { amplitude := 1, scale := 2 }
  | .far => { amplitude := 4, scale := 2 }
  | .tail => { amplitude := 8, scale := 4 }

def highAmplitude (window : Window) (packet : PDEPacket) : Prop :=
  packet.amplitude > 6 ∧ window = Window.tail

def highAmplitudeDecidable (window : Window) :
    Decidable (highAmplitude window (packetRunner window)) := by
  unfold highAmplitude packetRunner
  cases window <;> infer_instance

def eventContract : ScheduleEvents.FocusedContract.{1, 0, 0} focus :=
  PDE.CT6.focusedScheduleEvents pdeModel pdeState Window selectedWindows
    (fun _state _window => PDEPacket)
    (Focus.ActiveQuery.ofFunction fun _previous _active => packetRunner)
    (fun _previous _active window packet => highAmplitude window packet)
    (fun _previous _active window => highAmplitudeDecidable window)

def eventStage : eventContract.Stage :=
  eventContract.runStage ()

def eventHitActive : eventContract.hitFocus.Active eventStage := by
  refine ⟨trivial, ?_⟩
  unfold eventContract eventStage
  refine ⟨?_, rfl⟩
  refine ⟨Window.tail, ?_, ?_⟩
  · rw [eventContract.runStage_previous ()]
    change Window.tail ∈ windowSchedule.values
    decide
  · rw [eventContract.runStage_previous ()]
    change highAmplitude Window.tail (packetRunner Window.tail)
    simp [packetRunner, highAmplitude]

theorem event_hit_from_pde_schedule :
    ∃ window ∈ windowSchedule.values,
      highAmplitude window (packetRunner window) :=
  (@ScheduleEvents.FocusedContract.hitQuery.{1, 0, 0, 0, 0} Unit focus
    eventContract).read eventStage eventHitActive

def pdeEventRouteTarget :
    Execution.Spec eventContract.Stage where
  Input := fun _stage => Window
  Outcome := fun _stage _input => Unit
  Trace := fun _stage _input _outcome => Unit
  Sound := fun _stage _input _outcome _trace => True
  Exhaustive := fun _stage _input _outcome => True

def pdeEventRouteExecutor : Execution.Capability pdeEventRouteTarget where
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

def pdeEventRouteInput (stage : eventContract.Stage)
    (seed : ScheduleEventRoute.Seed stage) : Window :=
  seed.item

def pdeEventRouteEdge : Routing.Edge :=
  ⟨.ct6, .ct3, "pde-schedule-event-hit-route-fixture"⟩

noncomputable def pdeEventRouted :
    Routing.Stage
      (ScheduleEventRoute.transition pdeEventRouteEdge pdeEventRouteTarget
        pdeEventRouteExecutor pdeEventRouteInput) :=
  ScheduleEventRoute.advance pdeEventRouteEdge pdeEventRouteTarget
    pdeEventRouteExecutor pdeEventRouteInput eventStage

theorem pde_event_route_preserves_stage :
    pdeEventRouted.previous = eventStage :=
  ScheduleEventRoute.advance_previous pdeEventRouteEdge pdeEventRouteTarget
    pdeEventRouteExecutor pdeEventRouteInput eventStage

theorem pde_event_route_profile_enabled :
    ∃ seed,
      (ScheduleEventRoute.profile pdeEventRouteTarget pdeEventRouteExecutor
        pdeEventRouteInput).discover eventStage =
        Routing.Discovery.enabled seed := by
  refine ⟨ScheduleEventRoute.Seed.ofActive eventStage eventHitActive, ?_⟩
  change
    ((Routing.Profile.ofFocus
      eventContract.hitFocus
      pdeEventRouteTarget
      pdeEventRouteExecutor
      ScheduleEventRoute.Seed
      (fun stage active => ScheduleEventRoute.Seed.ofActive stage active)
      pdeEventRouteInput).discover eventStage) =
      Routing.Discovery.enabled
        (ScheduleEventRoute.Seed.ofActive eventStage eventHitActive)
  exact Routing.Profile.ofFocus_discover_active
    eventContract.hitFocus
    pdeEventRouteTarget
    pdeEventRouteExecutor
    ScheduleEventRoute.Seed
    (fun stage active => ScheduleEventRoute.Seed.ofActive stage active)
    pdeEventRouteInput
    eventStage eventHitActive

def extremeAmplitude (_window : Window) (packet : PDEPacket) : Prop :=
  packet.amplitude > 99

def extremeAmplitudeDecidable (window : Window) :
    Decidable (extremeAmplitude window (packetRunner window)) := by
  unfold extremeAmplitude packetRunner
  cases window <;> infer_instance

def noExtremeEventContract : ScheduleEvents.FocusedContract.{1, 0, 0} focus :=
  PDE.CT6.focusedScheduleEvents pdeModel pdeState Window selectedWindows
    (fun _state _window => PDEPacket)
    (Focus.ActiveQuery.ofFunction fun _previous _active => packetRunner)
    (fun _previous _active window packet => extremeAmplitude window packet)
    (fun _previous _active window => extremeAmplitudeDecidable window)

def noExtremeEventStage : noExtremeEventContract.Stage :=
  noExtremeEventContract.runStage ()

def noExtremeEventActive :
    noExtremeEventContract.noEventFocus.Active noExtremeEventStage := by
  refine ⟨trivial, ?_⟩
  unfold noExtremeEventContract noExtremeEventStage
  refine ⟨?_, rfl⟩
  intro existsHit
  rcases existsHit with ⟨window, member, event⟩
  rw [noExtremeEventContract.runStage_previous ()] at event
  cases window
  · change extremeAmplitude Window.near (packetRunner Window.near) at event
    simp [packetRunner, extremeAmplitude] at event
  · change extremeAmplitude Window.far (packetRunner Window.far) at event
    simp [packetRunner, extremeAmplitude] at event
  · change extremeAmplitude Window.tail (packetRunner Window.tail) at event
    simp [packetRunner, extremeAmplitude] at event

theorem no_extreme_packet_residual_output :
    ∀ window, (member : window ∈ windowSchedule.values) ->
      (((@ScheduleEvents.FocusedContract.pointwiseAbsentOutputQuery.{1, 0, 0, 0, 0}
        Unit focus noExtremeEventContract).read noExtremeEventStage
          noExtremeEventActive window member).1 = packetRunner window) := by
  intro window member
  rfl

theorem no_extreme_packet_residual_absent :
    ∀ window, (member : window ∈ windowSchedule.values) ->
      Not (extremeAmplitude window (packetRunner window)) :=
  (@ScheduleEvents.FocusedContract.pointwiseAbsentQuery.{1, 0, 0, 0, 0}
    Unit focus noExtremeEventContract).read noExtremeEventStage
      noExtremeEventActive

def pdeSilentResidual (_window : Window) (_packet : PDEPacket) : Prop :=
  True

theorem no_extreme_packet_remaining :
    ∀ window, window ∈ windowSchedule.values ->
      pdeSilentResidual window (packetRunner window) :=
  (@ScheduleEvents.FocusedContract.pointwiseRemainingQuery.{1, 0, 0, 0, 0}
      Unit focus noExtremeEventContract
      (fun _previous _active window packet =>
        pdeSilentResidual window packet)
      (fun _previous _active window _packet _absent => by
        unfold pdeSilentResidual
        trivial)).read noExtremeEventStage noExtremeEventActive

def scaleContract : ScaleRoute.FocusedScheduleContract.{1, 0} focus where
  Item := Window
  schedule := selectedWindows
  supportSize := fun _previous _active window =>
    (packetRunner window).amplitude
  scale := fun _previous _active window =>
    (packetRunner window).scale

def scaleStage : scaleContract.Stage :=
  scaleContract.runStage ()

def scaleLongActive : scaleContract.longFocus.Active scaleStage := by
  refine ⟨trivial, ?_⟩
  unfold scaleContract scaleStage
  refine ⟨?_, rfl⟩
  refine ⟨Window.far, ?_, ?_⟩
  · decide
  · change 2 < 4
    decide

theorem scale_route_detects_long_packet :
    scaleContract.AnyLong scaleStage.previous trivial :=
  (@ScaleRoute.FocusedScheduleContract.longQuery.{1, 0} Unit focus
    scaleContract).read scaleStage scaleLongActive

def responseItems :
    Focus.ActiveQuery focus fun _previous _active => List Window :=
  Focus.ActiveQuery.ofFunction fun _previous _active =>
    [Window.near, Window.far]

def responsePackage :
  Focus.ActiveQuery focus fun previous active =>
      (window : Window) -> window ∈ responseItems.read previous active ->
        Response.SameInterface.VerifiedPackage :=
  Focus.ActiveQuery.ofFunction fun _previous _active window _member =>
    { Source := Window
      Replacement := Window
      Interface := Nat
      Table := Nat
      source := window
      replacement := Window.near
      interface := (packetRunner window).scale
      table := (packetRunner window).amplitude
      boundaryCompatible := True
      sameResponse := True
      targetComplete := True
      boundaryCompatibleProof := trivial
      sameResponseProof := trivial
      targetCompleteProof := trivial }

def sameInterfaceContract : Response.SameInterface.Contract focus where
  Item := Window
  Package := Response.SameInterface.VerifiedPackage
  items := responseItems
  package := responsePackage

def sameInterfaceStage : sameInterfaceContract.Stage :=
  sameInterfaceContract.run ()

theorem same_interface_package_read
    (member : Window.near ∈ responseItems.read () trivial) :
    ((sameInterfaceContract.latestPackage.read sameInterfaceStage trivial)
      Window.near member).targetComplete :=
  trivial

def sameInterfaceSelectedItem :
    Focus.ActiveQuery sameInterfaceContract.successor fun _stage _active =>
      Window :=
  Focus.ActiveQuery.ofFunction fun _stage _active => Window.near

def sameInterfaceSelectedMember :
    Focus.ActiveQuery sameInterfaceContract.successor fun stage active =>
      sameInterfaceSelectedItem.read stage active ∈
        responseItems.read stage.previous active :=
  Focus.ActiveQuery.ofFunction fun stage active => by
    simp [sameInterfaceSelectedItem, responseItems]

theorem same_interface_target_complete_from_core_projection :
    ((sameInterfaceContract.latestPackageAt sameInterfaceSelectedItem
      sameInterfaceSelectedMember).read sameInterfaceStage
        trivial).targetComplete :=
  (sameInterfaceContract.latestPackageProof sameInterfaceSelectedItem
    sameInterfaceSelectedMember
    (fun package => package.targetComplete)
    (fun package => package.targetCompleteProof)).read sameInterfaceStage
      trivial

def pdeRouteSpec : Execution.Spec sameInterfaceContract.Stage where
  Input := fun _stage => PUnit
  Outcome := fun _stage _input => Nat
  Trace := fun _stage _input outcome => PLift (outcome = 1)
  Sound := fun _stage _input outcome _trace => outcome = 1
  Exhaustive := fun _stage _input outcome => outcome = 1

def pdeRouteCapability : Execution.Capability pdeRouteSpec where
  reference := fun _stage _input => ⟨⟨(1 : Nat), ⟨rfl⟩⟩, 1⟩
  sound := by
    intro stage input
    change (1 : Nat) = 1
    rfl
  exhaustive := by
    intro stage input
    change (1 : Nat) = 1
    rfl
  work := PolynomialCheckBudget.constant (fun _ => 1) 1
  checks_eq := by
    intro stage input
    rfl

def pdeRouteEdge : Routing.Edge :=
  ⟨.ct6, .ct3, "pde-focused-handoff-fixture"⟩

def pdeFocusedRouteProfile :
    Routing.Profile.{1, 0, 0, 0, 0, 0} sameInterfaceContract.Stage :=
  Routing.Profile.ofFocus
    sameInterfaceContract.successor
    pdeRouteSpec
    pdeRouteCapability
    (fun _stage => PUnit)
    (fun _stage _active => PUnit.unit)
    (fun _stage _seed => PUnit.unit)

def pdeFocusedTransition :
    Routing.Transition.{1, 0, 0, 0, 0, 0}
      pdeRouteEdge sameInterfaceContract.Stage :=
  Routing.Transition.register pdeRouteEdge pdeFocusedRouteProfile

def pdeFocusedRouted :
    Routing.Stage.{1, 0, 0, 0, 0, 0} pdeFocusedTransition :=
  Routing.advance pdeFocusedTransition sameInterfaceStage

theorem pde_focused_route_preserves_package_stage :
    pdeFocusedRouted.previous = sameInterfaceStage :=
  Routing.advance_previous pdeFocusedTransition sameInterfaceStage

theorem pde_focused_route_enabled :
    pdeFocusedRouted.added.discovery =
      Routing.Discovery.enabled PUnit.unit := by
  rfl

def ct3Schedule : Hypostructure.CT3.Schedule.Contract Window where
  items := windowSchedule
  terminal
    | .near => .compression
    | .far => .knownRow
    | .tail => .novelRow

def ct3Evidence : Hypostructure.CT3.ScheduleWitness.EvidenceContract
    ct3Schedule where
  GoodWitness := fun _window => Unit
  ResidualWitness := fun _window => Unit
  good_of_compression := fun _window _terminal => ()
  good_of_knownRow := fun _window _terminal => ()
  residual_of_distinguishing := fun _window _terminal => ()
  residual_of_novelRow := fun _window _terminal => ()

theorem ct3_terminal_split_available :
    ct3Schedule.AllGood ∨ ct3Schedule.HasResidual :=
  ct3Schedule.allGood_or_hasResidual

theorem ct3_residual_witness_available
    (hit : Hypostructure.Core.Finite.Search.IndexedHit
      ct3Schedule.items ct3Schedule.ResidualTerminal) :
    Nonempty (ct3Evidence.ResidualWitness hit.value) :=
  ct3Evidence.residualWitnessOfFirstHit hit

def ct3ResidualFocusedContract :
    Hypostructure.CT3.Schedule.FocusedContract focus where
  Item := Window
  items := selectedWindows
  terminal := fun _previous _active window =>
    match window with
    | .near => .distinguishing
    | .far => .knownRow
    | .tail => .compression

def ct3ResidualStage :=
  ct3ResidualFocusedContract.runStage ()

def ct3ResidualEvidence (previous : Unit) (active : focus.Active previous) :
    Hypostructure.CT3.ScheduleWitness.EvidenceContract
      (ct3ResidualFocusedContract.scheduleAt previous active) where
  GoodWitness := fun _window => PDEPacket
  ResidualWitness := fun _window => PDEPacket
  good_of_compression := fun window _terminal => packetRunner window
  good_of_knownRow := fun window _terminal => packetRunner window
  residual_of_distinguishing := fun window _terminal => packetRunner window
  residual_of_novelRow := fun window _terminal => packetRunner window

def pdeResidualRouteTarget :
    Execution.Spec ct3ResidualFocusedContract.Stage where
  Input := fun _stage => Window
  Outcome := fun _stage _input => Unit
  Trace := fun _stage _input _outcome => Unit
  Sound := fun _stage _input _outcome _trace => True
  Exhaustive := fun _stage _input _outcome => True

def pdeResidualRouteExecutor :
    Execution.Capability pdeResidualRouteTarget where
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

noncomputable def pdeResidualRouteContract :
    Hypostructure.CT3.ResidualRoute.Contract
      ct3ResidualFocusedContract where
  evidence := ct3ResidualEvidence
  target := pdeResidualRouteTarget
  executor := pdeResidualRouteExecutor
  targetInput := fun _stage seed => seed.hit.value

def pdeResidualRouteEdge : Routing.Edge :=
  ⟨.ct3, .ct7, "pde-ct3-residual-route-fixture"⟩

noncomputable def pdeResidualRouted :
    Routing.Stage
      (pdeResidualRouteContract.transition pdeResidualRouteEdge) :=
  Hypostructure.PDE.CT3.advanceClassifiedResidualRoute
    pdeResidualRouteContract pdeResidualRouteEdge ()

theorem pde_residual_route_preserves_stage :
    pdeResidualRouted.previous = ct3ResidualStage :=
  pdeResidualRouteContract.advanceClassified_previous pdeResidualRouteEdge ()

theorem pde_residual_route_source_previous :
    pdeResidualRouted.previous.previous = () :=
  Hypostructure.PDE.CT3.advanceClassifiedResidualRoute_source_previous
    pdeResidualRouteContract pdeResidualRouteEdge ()

theorem pde_residual_route_profile_enabled
    (active : ct3ResidualFocusedContract.residualFocus.Active
      ct3ResidualStage) :
    ∃ seed,
      pdeResidualRouteContract.profile.discover ct3ResidualStage =
        Routing.Discovery.enabled seed := by
  refine ⟨
    Hypostructure.CT3.ResidualRoute.Seed.ofActive
      ct3ResidualEvidence ct3ResidualStage active, ?_⟩
  change
    ((Routing.Profile.ofFocus
      ct3ResidualFocusedContract.residualFocus
      pdeResidualRouteTarget
      pdeResidualRouteExecutor
      (Hypostructure.CT3.ResidualRoute.Seed ct3ResidualEvidence)
      (fun stage active =>
        Hypostructure.CT3.ResidualRoute.Seed.ofActive
          ct3ResidualEvidence stage active)
      (fun _stage seed => seed.hit.value)).discover ct3ResidualStage) =
      Routing.Discovery.enabled
        (Hypostructure.CT3.ResidualRoute.Seed.ofActive
          ct3ResidualEvidence ct3ResidualStage active)
  exact Routing.Profile.ofFocus_discover_active
    ct3ResidualFocusedContract.residualFocus
    pdeResidualRouteTarget
    pdeResidualRouteExecutor
    (Hypostructure.CT3.ResidualRoute.Seed ct3ResidualEvidence)
    (fun stage active =>
      Hypostructure.CT3.ResidualRoute.Seed.ofActive
        ct3ResidualEvidence stage active)
    (fun _stage seed => seed.hit.value)
    ct3ResidualStage active

def ct3GoodScheduleQuery :
    Focus.ActiveQuery focus fun _previous _active => Enumeration Window :=
  Focus.ActiveQuery.ofFunction fun _previous _active =>
    Enumeration.ofNodupList [Window.near, Window.far] (by decide)

def ct3GoodFocusedContract :
    Hypostructure.CT3.Schedule.FocusedContract focus where
  Item := Window
  items := ct3GoodScheduleQuery
  terminal := fun _previous _active window =>
    match window with
    | .near => .compression
    | .far => .knownRow
    | .tail => .novelRow

def ct3GoodStage := ct3GoodFocusedContract.runStage ()

def ct3GoodEvidence (previous : Unit) (active : focus.Active previous) :
    Hypostructure.CT3.ScheduleWitness.EvidenceContract
      (ct3GoodFocusedContract.scheduleAt previous active) where
  GoodWitness := fun _window => Unit
  ResidualWitness := fun _window => Unit
  good_of_compression := fun _window _terminal => ()
  good_of_knownRow := fun _window _terminal => ()
  residual_of_distinguishing := fun _window _terminal => ()
  residual_of_novelRow := fun _window _terminal => ()

def ct3GoodSameInterfaceContract :
    Hypostructure.CT3.SameInterface.PackageContract
      ct3GoodFocusedContract where
  evidence := ct3GoodEvidence
  packageOfGood := fun _previous _active window _good _witness =>
    { Source := Window
      Replacement := Window
      Interface := Nat
      Table := Nat
      source := window
      replacement := Window.near
      interface := (packetRunner window).scale
      table := (packetRunner window).amplitude
      boundaryCompatible := True
      sameResponse := True
      targetComplete := True
      boundaryCompatibleProof := trivial
      sameResponseProof := trivial
      targetCompleteProof := trivial }

noncomputable def ct3GoodPackageStage :=
  Hypostructure.PDE.CT3.registerClassifiedSameInterface
    ct3GoodSameInterfaceContract ()

theorem ct3_good_package_stage_source_previous :
    ct3GoodPackageStage.previous.previous = () :=
  Hypostructure.PDE.CT3.registerClassifiedSameInterface_source_previous
    ct3GoodSameInterfaceContract ()

noncomputable def ct3GoodPackageItem :
    Focus.ActiveQuery
      (ct3GoodSameInterfaceContract.sameInterfaceContract).successor
        fun _stage _active => Window :=
  Focus.ActiveQuery.ofFunction fun _stage _active => Window.near

noncomputable def ct3GoodPackageMember :
    Focus.ActiveQuery
      (ct3GoodSameInterfaceContract.sameInterfaceContract).successor
        fun stage active =>
          ct3GoodPackageItem.read stage active ∈
            (ct3GoodSameInterfaceContract.sameInterfaceContract).items.read
              stage.previous active :=
  Focus.ActiveQuery.ofFunction fun _stage _active => by
    change Window.near ∈
      (Enumeration.ofNodupList [Window.near, Window.far] (by decide)).values
    decide

theorem ct3_good_same_interface_target_complete
    (active :
      (ct3GoodSameInterfaceContract.sameInterfaceContract).successor.Active
        ct3GoodPackageStage) :
    (((ct3GoodSameInterfaceContract.sameInterfaceContract).latestPackageAt
      ct3GoodPackageItem ct3GoodPackageMember).read
        ct3GoodPackageStage active).targetComplete :=
  ((ct3GoodSameInterfaceContract.sameInterfaceContract).latestPackageProof
    ct3GoodPackageItem ct3GoodPackageMember
    (fun package => package.targetComplete)
    (fun package => package.targetCompleteProof)).read
      ct3GoodPackageStage active

theorem ct3_good_verified_same_interface_target_complete
    (active :
      (ct3GoodSameInterfaceContract.verifiedSameInterfaceContract).successor.Active
        ct3GoodPackageStage) :
    (((ct3GoodSameInterfaceContract.verifiedSameInterfaceContract).latestPackageAt
      ct3GoodPackageItem ct3GoodPackageMember).read
        ct3GoodPackageStage active).targetComplete :=
  ((ct3GoodSameInterfaceContract.verifiedSameInterfaceContract).latestTargetComplete
    ct3GoodPackageItem ct3GoodPackageMember).read
      ct3GoodPackageStage active

#print axioms selected_card_from_ledger
#print axioms selected_card_exact_from_ledger
#print axioms selected_attached_card_from_ledger
#print axioms selected_attached_windows_from_ledger
#print axioms partition_card_exact
#print axioms flattened_atom_count
#print axioms event_hit_from_pde_schedule
#print axioms pde_event_route_preserves_stage
#print axioms pde_event_route_profile_enabled
#print axioms no_extreme_packet_residual_output
#print axioms no_extreme_packet_residual_absent
#print axioms no_extreme_packet_remaining
#print axioms scale_route_detects_long_packet
#print axioms same_interface_package_read
#print axioms same_interface_target_complete_from_core_projection
#print axioms pde_focused_route_preserves_package_stage
#print axioms pde_focused_route_enabled
#print axioms ct3_terminal_split_available
#print axioms ct3_residual_witness_available
#print axioms pde_residual_route_preserves_stage
#print axioms pde_residual_route_source_previous
#print axioms pde_residual_route_profile_enabled
#print axioms ct3_good_same_interface_target_complete
#print axioms ct3_good_verified_same_interface_target_complete
#print axioms ct3_good_package_stage_source_previous

end Hypostructure.Fixtures.ColdBranchPDETransfer
