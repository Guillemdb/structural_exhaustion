import Hypostructure.PDE.Contract
import HypostructurePDEExamples.RepresentedNS2DDefectRoutingPacket

/-!
# Represented 2D Navier--Stokes row-7 capacity packet

The represented row-6 packet is inactive because row 5 already reached the
positive structural-gap terminal.  Row 7 is nevertheless instantiated against
the literal row-6 successor.  Core evaluates the capacity-ready focus, skips
the CT14/CT1 payload on this inactive sibling, and preserves the exact
predecessor ledger.
-/

namespace HypostructurePDEExamples.RepresentedNS2DCapacityTargetCompactificationPacket

open Hypostructure
open Hypostructure.Core
open Hypostructure.Core.Residual
open Hypostructure.PDE.FastTrack
open HypostructurePDEExamples.RepresentedNS2DDirectedExhaustivenessPacket
open HypostructurePDEExamples.RepresentedNS2DDefectRoutingPacket

noncomputable section

abbrev RowSixProfile := rowSixProfile
abbrev RowSixStage := CapacityProfile.RowSixStage RowSixProfile
abbrev CapacityView := CapacityProfile.ActiveView RowSixProfile

def viewQuery : Residual.Query CapacityView fun _view => CapacityView :=
  Residual.Query.residual

def memberSchedule : Core.Finite.Enumeration (Fin 1) :=
  Core.Finite.Enumeration.singleton 0

def membersQuery :
    Residual.Query CapacityView fun _view =>
      Core.Finite.Enumeration (Fin 1) :=
  viewQuery.map fun _view _root => memberSchedule

def capacitySpec : CT14.Spec CapacityView where
  Member := fun _view => Fin 1
  Label := fun _view => Unit
  memberLowerMass := fun _view _member => 0
  memberCapacity := fun _view _member => some 0
  memberLabel := fun _view _member => some ()

def capacityCapability : CT14.Capability capacitySpec where
  members := membersQuery
  labelDecidableEq := fun _view => by
    change DecidableEq Unit
    infer_instance
  inputSize := fun _view => 0
  workCoefficient := 4
  workDegree := 0
  workBound := by
    intro _view
    change CT14.localCheckBound memberSchedule <= 4
    decide

abbrev TargetPrevious :=
  CT14.Stage capacitySpec capacityCapability

def targetSchedule : Core.Finite.Enumeration Unit :=
  Core.Finite.Enumeration.empty Unit

def targetQuery :
    Residual.Query TargetPrevious fun _previous =>
      Core.Finite.Enumeration Unit :=
  Residual.Query.residual.map fun _previous _root => targetSchedule

def targetSpec : CT1.Spec TargetPrevious where
  Candidate := fun _previous => Unit
  Realizes := fun _previous _candidate => False

def targetCapability : CT1.Capability targetSpec where
  schedule := targetQuery
  realizesDecidable := fun _previous _candidate => isFalse id
  inputSize := fun _previous => 0
  workCoefficient := 1
  workDegree := 0
  workBound := by
    intro _previous
    simp [CT1.searchCheckBound, targetQuery, targetSchedule,
      Core.Finite.Enumeration.card]
    exact Nat.zero_le 1

def rowSevenContract : PDE.Contract.CapacityTarget RowSixProfile :=
  PDE.Contract.CapacityTarget.ofCapabilityCanonicalEnvelope
    capacitySpec capacityCapability targetSpec targetCapability

abbrev rowSevenProfile : CapacityProfile.Profile RowSixProfile :=
  rowSevenContract.toCapacityProfile

def rowSevenRun :=
  rowSevenContract.run rowSixRun.value

theorem rowSeven_retains_literal_row_six :
    rowSevenRun.value.previous = rowSixRun.value :=
  rowSevenContract.run_previous rowSixRun.value

theorem rowSeven_capacity_ready_inactive :
    Not (RowSixProfile.CapacityReadyFocus.Active rowSixRun.value) := by
  intro active
  have parentActive :
      (DirectedExhaustiveness.Profile.TargetVisibleFocus
        rowFiveProfile).Active rowSixRun.value.previous := by
    have parent := active.parent
    change (DirectedExhaustiveness.Profile.TargetVisibleFocus
      rowFiveProfile).Active rowSixRun.value.previous at parent
    exact parent
  rw [rowSix_retains_literal_rowFive] at parentActive
  exact rowFiveTargetVisibleInactive parentActive

theorem rowSeven_skips_inactive_payload :
    rowSevenRun.checks =
      RowSixProfile.CapacityReadyFocus.selectionBudget.checks rowSixRun.value :=
  rowSevenContract.run_checks_of_inactive rowSixRun.value
    rowSeven_capacity_ready_inactive

theorem rowSeven_work_is_bounded :
    rowSevenRun.checks <=
      (RowSixProfile.CapacityReadyFocus.selectionBudget.add
        (CapacityProfile.payloadBudget rowSevenProfile)).coefficient *
      ((RowSixProfile.CapacityReadyFocus.selectionBudget.add
        (CapacityProfile.payloadBudget rowSevenProfile)).size rowSixRun.value + 1) ^
      (RowSixProfile.CapacityReadyFocus.selectionBudget.add
        (CapacityProfile.payloadBudget rowSevenProfile)).degree :=
  rowSevenContract.run_checks_bounded rowSixRun.value

#print axioms rowSeven_skips_inactive_payload
#print axioms rowSeven_work_is_bounded

end

end HypostructurePDEExamples.RepresentedNS2DCapacityTargetCompactificationPacket
