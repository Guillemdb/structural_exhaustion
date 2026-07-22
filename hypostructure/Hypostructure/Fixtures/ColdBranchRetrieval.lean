import Hypostructure.Core.Finite.SelectedSchedule
import Hypostructure.Core.Response.SameInterface
import Hypostructure.Core.Routing
import Hypostructure.CT3.ResidualRoute
import Hypostructure.CT3.SameInterface
import Hypostructure.CT3.ScheduleWitness

/-!
# Cold-branch retrieval fixtures

Neutral fixtures for selected schedule projection, CT3 terminal witness
extraction, and same-interface package registration/retrieval.  These are
domain-independent APIs used by graph and PDE contracts.
-/

namespace Hypostructure.Fixtures.ColdBranchRetrieval

open Hypostructure.Core
open Hypostructure.Core.Finite
open Hypostructure.Core.Residual

abbrev focus : Focus.Profile Nat :=
  Focus.always Nat

def scheduleQuery : Focus.ActiveQuery focus fun _previous _active =>
    Enumeration Nat :=
  Focus.ActiveQuery.ofFunction fun _previous _active =>
    Enumeration.ofNodupList [0, 1] (by decide)

def selectedContract : SelectedSchedule.Contract focus where
  Item := Nat
  selected := scheduleQuery

def selectedStage := selectedContract.execute 0

theorem selected_preserves_previous :
    selectedStage.previous = 0 :=
  selectedContract.execute_previous 0

theorem selected_latest_card :
    selectedContract.latestCard.read selectedStage trivial = 2 := by
  rfl

theorem selected_latest_card_exact :
    selectedContract.latestCard.read selectedStage trivial =
      (scheduleQuery.read 0 trivial).card :=
  selectedContract.latestCardExact.read selectedStage trivial

def ct3Schedule : Hypostructure.CT3.Schedule.Contract Nat where
  items := Enumeration.ofNodupList [0, 1] (by decide)
  terminal
    | 0 => .compression
    | _ => .knownRow

def ct3Evidence : Hypostructure.CT3.ScheduleWitness.EvidenceContract
    ct3Schedule where
  GoodWitness := fun _ => Unit
  ResidualWitness := fun _ => Unit
  good_of_compression := fun _ _ => ()
  good_of_knownRow := fun _ _ => ()
  residual_of_distinguishing := fun _ _ => ()
  residual_of_novelRow := fun _ _ => ()

theorem ct3_good_witnesses (allGood : ct3Schedule.AllGood) :
    ct3Evidence.allGoodWitnesses allGood :=
  ct3Evidence.allGoodWitnesses_of_allGood allGood

def ct3ResidualSchedule : Hypostructure.CT3.Schedule.Contract Nat where
  items := Enumeration.ofNodupList [0, 1] (by decide)
  terminal
    | 0 => .distinguishing
    | _ => .knownRow

def ct3ResidualEvidence : Hypostructure.CT3.ScheduleWitness.EvidenceContract
    ct3ResidualSchedule where
  GoodWitness := fun _ => Unit
  ResidualWitness := fun _ => Unit
  good_of_compression := fun _ _ => ()
  good_of_knownRow := fun _ _ => ()
  residual_of_distinguishing := fun _ _ => ()
  residual_of_novelRow := fun _ _ => ()

theorem ct3_first_residual_witness
    (hit : Hypostructure.Core.Finite.Search.IndexedHit
      ct3ResidualSchedule.items ct3ResidualSchedule.ResidualTerminal) :
    Nonempty (ct3ResidualEvidence.ResidualWitness hit.value) :=
  ct3ResidualEvidence.residualWitnessOfFirstHit hit

def focusedAllGoodSchedule :
    Focus.ActiveQuery focus fun _previous _active => Enumeration Nat :=
  Focus.ActiveQuery.ofFunction fun _previous _active =>
    Enumeration.ofNodupList [0, 1] (by decide)

def focusedAllGoodContract :
    Hypostructure.CT3.Schedule.FocusedContract focus where
  Item := Nat
  items := focusedAllGoodSchedule
  terminal := fun _previous _active item =>
    match item with
    | 0 => .compression
    | _ => .knownRow

def focusedAllGoodStage := focusedAllGoodContract.runStage 0

theorem focused_allGood_query_reads
    (active : focusedAllGoodContract.allGoodFocus.Active
      focusedAllGoodStage) :
    ∀ item ∈ (focusedAllGoodSchedule.read 0 trivial).values,
      Hypostructure.CT3.Schedule.Contract.GoodTerminal
        (focusedAllGoodContract.scheduleAt 0 trivial) item :=
  focusedAllGoodContract.allGoodQuery.read focusedAllGoodStage
    active

def focusedAllGoodEvidence (previous : Nat) (active : focus.Active previous) :
    Hypostructure.CT3.ScheduleWitness.EvidenceContract
      (focusedAllGoodContract.scheduleAt previous active) where
  GoodWitness := fun _ => Unit
  ResidualWitness := fun _ => Unit
  good_of_compression := fun _ _ => ()
  good_of_knownRow := fun _ _ => ()
  residual_of_distinguishing := fun _ _ => ()
  residual_of_novelRow := fun _ _ => ()

def focusedAllGoodPackageContract :
    Hypostructure.CT3.SameInterface.PackageContract
      focusedAllGoodContract where
  evidence := focusedAllGoodEvidence
  packageOfGood := fun _previous _active _item _good _witness =>
    { Source := Unit
      Replacement := Unit
      Interface := Unit
      Table := Unit
      source := ()
      replacement := ()
      interface := ()
      table := ()
      boundaryCompatible := True
      sameResponse := True
      targetComplete := True
      boundaryCompatibleProof := trivial
      sameResponseProof := trivial
      targetCompleteProof := trivial }

noncomputable def focusedAllGoodPackageStage :=
  focusedAllGoodPackageContract.register focusedAllGoodStage

noncomputable def focusedAllGoodPackageItem :
    Focus.ActiveQuery
      (focusedAllGoodPackageContract.sameInterfaceContract).successor
        fun _stage _active => Nat :=
  Focus.ActiveQuery.ofFunction fun _stage _active => 0

noncomputable def focusedAllGoodPackageMember :
    Focus.ActiveQuery
      (focusedAllGoodPackageContract.sameInterfaceContract).successor
        fun stage active =>
          focusedAllGoodPackageItem.read stage active ∈
            (focusedAllGoodPackageContract.sameInterfaceContract).items.read
              stage.previous active :=
  Focus.ActiveQuery.ofFunction fun stage active => by
    change 0 ∈ (Enumeration.ofNodupList [0, 1] (by decide)).values
    decide

theorem focused_allGood_package_target_complete
    (active :
      (focusedAllGoodPackageContract.sameInterfaceContract).successor.Active
        focusedAllGoodPackageStage) :
    (((focusedAllGoodPackageContract.sameInterfaceContract).latestPackageAt
      focusedAllGoodPackageItem focusedAllGoodPackageMember).read
        focusedAllGoodPackageStage active).targetComplete :=
  ((focusedAllGoodPackageContract.sameInterfaceContract).latestPackageProof
    focusedAllGoodPackageItem focusedAllGoodPackageMember
    (fun package => package.targetComplete)
    (fun package => package.targetCompleteProof)).read
      focusedAllGoodPackageStage active

theorem focused_allGood_verified_target_complete
    (active :
      (focusedAllGoodPackageContract.verifiedSameInterfaceContract).successor.Active
        focusedAllGoodPackageStage) :
    (((focusedAllGoodPackageContract.verifiedSameInterfaceContract).latestPackageAt
      focusedAllGoodPackageItem focusedAllGoodPackageMember).read
        focusedAllGoodPackageStage active).targetComplete :=
  ((focusedAllGoodPackageContract.verifiedSameInterfaceContract).latestTargetComplete
    focusedAllGoodPackageItem focusedAllGoodPackageMember).read
      focusedAllGoodPackageStage active

def focusedResidualSchedule :
    Focus.ActiveQuery focus fun _previous _active => Enumeration Nat :=
  Focus.ActiveQuery.ofFunction fun _previous _active =>
    Enumeration.ofNodupList [0, 1] (by decide)

def focusedResidualContract :
    Hypostructure.CT3.Schedule.FocusedContract focus where
  Item := Nat
  items := focusedResidualSchedule
  terminal := fun _previous _active item =>
    match item with
    | 0 => .distinguishing
    | _ => .knownRow

def focusedResidualStage := focusedResidualContract.runStage 0

theorem focused_residual_query_reads
    (active : focusedResidualContract.residualFocus.Active
      focusedResidualStage) :
    ∃ item ∈ (focusedResidualSchedule.read 0 trivial).values,
      Hypostructure.CT3.Schedule.Contract.ResidualTerminal
        (focusedResidualContract.scheduleAt 0 trivial) item :=
  focusedResidualContract.hasResidualQuery.read focusedResidualStage
    active

theorem focused_residual_terminal_query_reads
    (active : focusedResidualContract.residualFocus.Active
      focusedResidualStage) :
    Hypostructure.CT3.Schedule.Contract.ResidualTerminal
      (focusedResidualContract.scheduleAt 0 trivial)
      (focusedResidualContract.residualItemQuery.read focusedResidualStage
        active) :=
  focusedResidualContract.residualTerminalQuery.read focusedResidualStage
    active

def focusedResidualEvidence (previous : Nat) (active : focus.Active previous) :
    Hypostructure.CT3.ScheduleWitness.EvidenceContract
      (focusedResidualContract.scheduleAt previous active) where
  GoodWitness := fun _ => Unit
  ResidualWitness := fun _ => Unit
  good_of_compression := fun _ _ => ()
  good_of_knownRow := fun _ _ => ()
  residual_of_distinguishing := fun _ _ => ()
  residual_of_novelRow := fun _ _ => ()

def residualRouteTarget :
    Execution.Spec focusedResidualContract.Stage where
  Input := fun _stage => Nat
  Outcome := fun _stage _input => Unit
  Trace := fun _stage _input _outcome => Unit
  Sound := fun _stage _input _outcome _trace => True
  Exhaustive := fun _stage _input _outcome => True

def residualRouteExecutor : Execution.Capability residualRouteTarget where
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

noncomputable def focusedResidualRouteContract :
    Hypostructure.CT3.ResidualRoute.Contract
      focusedResidualContract where
  evidence := focusedResidualEvidence
  target := residualRouteTarget
  executor := residualRouteExecutor
  targetInput := fun _stage seed => seed.hit.value

def focusedResidualRouteEdge : Routing.Edge :=
  ⟨.ct3, .ct7, "neutral-ct3-residual-route-fixture"⟩

noncomputable def focusedResidualRouted :
    Routing.Stage
      (focusedResidualRouteContract.transition focusedResidualRouteEdge) :=
  focusedResidualRouteContract.advance focusedResidualRouteEdge
    focusedResidualStage

theorem focused_residual_route_preserves_stage :
    focusedResidualRouted.previous = focusedResidualStage :=
  focusedResidualRouteContract.advance_previous focusedResidualRouteEdge
    focusedResidualStage

theorem focused_residual_route_enabled :
    (active : focusedResidualContract.residualFocus.Active
      focusedResidualStage) ->
    ∃ seed,
      focusedResidualRouteContract.profile.discover focusedResidualStage =
        Routing.Discovery.enabled seed := by
  intro active
  refine ⟨
    Hypostructure.CT3.ResidualRoute.Seed.ofActive
      focusedResidualEvidence focusedResidualStage active, ?_⟩
  change
    ((Routing.Profile.ofFocus
      focusedResidualContract.residualFocus
      residualRouteTarget
      residualRouteExecutor
      (Hypostructure.CT3.ResidualRoute.Seed focusedResidualEvidence)
      (fun stage active =>
        Hypostructure.CT3.ResidualRoute.Seed.ofActive
          focusedResidualEvidence stage active)
      (fun _stage seed => seed.hit.value)).discover focusedResidualStage) =
      Routing.Discovery.enabled
        (Hypostructure.CT3.ResidualRoute.Seed.ofActive
          focusedResidualEvidence focusedResidualStage active)
  exact Routing.Profile.ofFocus_discover_active
    focusedResidualContract.residualFocus
    residualRouteTarget
    residualRouteExecutor
    (Hypostructure.CT3.ResidualRoute.Seed focusedResidualEvidence)
    (fun stage active =>
      Hypostructure.CT3.ResidualRoute.Seed.ofActive
        focusedResidualEvidence stage active)
    (fun _stage seed => seed.hit.value)
    focusedResidualStage active

def packageItems : Focus.ActiveQuery focus fun _previous _active => List Nat :=
  Focus.ActiveQuery.ofFunction fun _previous _active => [0, 1]

def packageQuery : Focus.ActiveQuery focus fun previous active =>
    (item : Nat) -> item ∈ packageItems.read previous active -> String :=
  Focus.ActiveQuery.ofFunction fun _previous _active item _member =>
    toString item

def sameInterfaceContract : Response.SameInterface.Contract focus where
  Item := Nat
  Package := String
  items := packageItems
  package := packageQuery

def packageStage := sameInterfaceContract.register 0

theorem package_preserves_previous :
    packageStage.previous = 0 :=
  sameInterfaceContract.register_previous 0

def selectedPackageItem :
    Focus.ActiveQuery sameInterfaceContract.successor fun _stage _active =>
      Nat :=
  Focus.ActiveQuery.ofFunction fun _stage _active => 1

def selectedPackageMember :
    Focus.ActiveQuery sameInterfaceContract.successor fun stage active =>
      selectedPackageItem.read stage active ∈
        packageItems.read stage.previous active :=
  Focus.ActiveQuery.ofFunction fun stage active => by
    simp [selectedPackageItem, packageItems]

theorem package_at_reads :
    (sameInterfaceContract.latestPackageAt selectedPackageItem
      selectedPackageMember).read packageStage trivial = "1" :=
  rfl

#print axioms selected_preserves_previous
#print axioms selected_latest_card
#print axioms selected_latest_card_exact
#print axioms ct3_good_witnesses
#print axioms ct3_first_residual_witness
#print axioms focused_allGood_query_reads
#print axioms focused_allGood_package_target_complete
#print axioms focused_allGood_verified_target_complete
#print axioms focused_residual_query_reads
#print axioms focused_residual_terminal_query_reads
#print axioms focused_residual_route_preserves_stage
#print axioms focused_residual_route_enabled
#print axioms package_preserves_previous
#print axioms package_at_reads

end Hypostructure.Fixtures.ColdBranchRetrieval
