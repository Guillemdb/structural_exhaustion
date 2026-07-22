import Hypostructure.PDE.Contract
import HypostructurePDEExamples.RepresentedNS2DBoundaryRepairPacket

/-!
# Represented 2D Navier--Stokes row-11 conservative-carrier packet

The represented row-10 packet is inactive because the row-9 successor is
inactive. Row 11 is still instantiated over the literal row-10 successor.
Core skips the CT5-to-CT14-to-CT11 payload on the inactive successor and
retains the predecessor ledger.
-/

namespace HypostructurePDEExamples.RepresentedNS2DConservativeCarrierPacket

open Hypostructure
open Hypostructure.Core
open Hypostructure.Core.Residual
open Hypostructure.PDE.FastTrack
open HypostructurePDEExamples.RepresentedNS2DBoundaryRepairPacket

noncomputable section

abbrev RowTenProfile := rowTenProfile
abbrev RowTenStage := ConservativeCarrier.RowTenStage RowTenProfile
abbrev RowElevenView := ConservativeCarrier.ActiveView RowTenProfile

def rowTenStage : RowTenStage :=
  rowTenRun.value

theorem rowTenSuccessorInactive :
    Not ((BoundaryRepair.SuccessorFocus RowTenProfile).Active
      rowTenStage) := by
  intro active
  change
    (ProfileFamily.SuccessorFocus RowNineProfile).Active
      rowTenRun.value.previous at active
  rw [rowTen_retains_literal_row_nine] at active
  exact rowNineSuccessorInactive active

abbrev natResourceBudget : Core.ResourceBudget where
  Resource := Nat
  le := (· <= ·)
  leRefl := by intro r; exact Nat.le_refl r
  leTrans := by intro a b c hab hbc; exact Nat.le_trans hab hbc
  zero := 0
  add := (· + ·)
  ceiling := id
  zeroLe := by intro r; exact Nat.zero_le r
  addMono := by intro a b c d hab hcd; exact Nat.add_le_add hab hcd
  addAssoc := by intro a b c; exact Nat.add_assoc a b c
  zeroAdd := by intro a; exact Nat.zero_add a
  addZero := by intro a; exact Nat.add_zero a

abbrev carrierSpec : CT5.Spec RowElevenView where
  budget := natResourceBudget
  Site := fun _previous => Unit
  Witness := fun _previous _site => Unit
  Active := fun _previous _site => True
  Supports := fun _previous _site _witness => True
  contribution := fun _previous _site _witness => (0 : Nat)
  required := fun _previous => (0 : Nat)
  capacity := fun _previous => (0 : Nat)

def carrierFamilyQuery :
    Residual.Query RowElevenView fun previous =>
      Core.Finite.DependentEnumeration (carrierSpec.Site previous)
        (carrierSpec.Witness previous) :=
  Residual.Query.residual.map fun _previous _root => {
    indices := Core.Finite.Enumeration.singleton ()
    fibres := fun _site => Core.Finite.Enumeration.singleton ()
  }

def carrierCapability : CT5.Capability carrierSpec where
  family := carrierFamilyQuery
  activeDecidable := fun _previous _site => isTrue trivial
  supportsDecidable := fun _previous _site _witness => isTrue trivial
  resourceLEDecidable := fun left right =>
    inferInstanceAs (Decidable (left <= right))

abbrev CarrierStage :=
  CT5.Stage carrierSpec carrierCapability

abbrev capacitySpec : CT14.Spec CarrierStage where
  Member := fun _previous => Unit
  Label := fun _previous => Unit
  memberLowerMass := fun _previous _member => 1
  memberCapacity := fun _previous _member => some 0
  memberLabel := fun _previous _member => some ()

def memberQuery :
    Residual.Query CarrierStage fun _previous =>
      Core.Finite.Enumeration Unit :=
  Residual.Query.residual.map fun _previous _root =>
    Core.Finite.Enumeration.singleton ()

def capacityCapability : CT14.Capability capacitySpec where
  members := memberQuery
  labelDecidableEq := fun _previous => by
    change DecidableEq Unit
    infer_instance
  inputSize := fun _previous => 0
  workCoefficient := 4
  workDegree := 0
  workBound := by
    intro previous
    change CT14.localCheckBound (Core.Finite.Enumeration.singleton ()) <=
      4 * (0 + 1) ^ 0
    decide

abbrev CapacityStage :=
  CT14.Stage capacitySpec capacityCapability

def cellQuery :
    Residual.Query CapacityStage fun _previous =>
      Core.Finite.Enumeration Unit :=
  Residual.Query.residual.map fun _previous _root =>
    Core.Finite.Enumeration.singleton ()

def negativeTotalQuery :
    Residual.Query CapacityStage fun previous =>
      ((cellQuery.read previous).values.map (fun _cell : Unit => (-1 : Int))).sum <
        0 :=
  Residual.Query.residual.map fun (_previous : CapacityStage) _root => by
    change (([()].map (fun _cell : Unit => (-1 : Int))).sum < 0)
    decide

def budgetProfile : CT11.OrderedNegativeBudgetProfile CapacityStage where
  Cell := fun _previous => Unit
  localBudget := fun _previous _cell => -1
  cells := cellQuery
  negativeTotal := negativeTotalQuery
  inputSize := fun _previous => 0
  workCoefficient := 2
  workDegree := 0
  workBound := by
    intro previous
    change CT11.localCheckBound (Core.Finite.Enumeration.singleton ()) <= 2
    decide

abbrev budgetSpec : CT11.Spec CapacityStage :=
  budgetProfile.spec

def budgetCapability : CT11.Capability budgetSpec :=
  budgetProfile.capability

def rowElevenContract :
    PDE.Contract.ConservativeCarrierContract RowTenProfile :=
  PDE.Contract.ConservativeCarrierContract.ofCapabilityCanonicalEnvelope
    carrierSpec carrierCapability capacitySpec capacityCapability
    budgetSpec budgetCapability

abbrev rowElevenProfile : ConservativeCarrier.Profile RowTenProfile :=
  rowElevenContract.toProfile

def rowElevenRun :=
  rowElevenContract.run rowTenStage

theorem rowEleven_retains_literal_row_ten :
    rowElevenRun.value.previous = rowTenStage :=
  rowElevenContract.run_previous rowTenStage

theorem rowEleven_skips_inactive_payload :
    rowElevenRun.checks =
      (BoundaryRepair.SuccessorFocus RowTenProfile).selectionBudget.checks
        rowTenStage :=
  rowElevenContract.run_checks_of_inactive rowTenStage rowTenSuccessorInactive

theorem rowEleven_work_is_bounded :
    rowElevenRun.checks <=
      ((BoundaryRepair.SuccessorFocus RowTenProfile).selectionBudget.add
        (ConservativeCarrier.payloadBudget rowElevenProfile)).coefficient *
      (((BoundaryRepair.SuccessorFocus RowTenProfile).selectionBudget.add
        (ConservativeCarrier.payloadBudget rowElevenProfile)).size
          rowTenStage + 1) ^
      ((BoundaryRepair.SuccessorFocus RowTenProfile).selectionBudget.add
        (ConservativeCarrier.payloadBudget rowElevenProfile)).degree :=
  rowElevenContract.run_checks_bounded rowTenStage

theorem rowEleven_retains_root_residual :
    Core.Residual.residualOf rowElevenRun.value =
      HypostructurePDEExamples.RepresentedNS2DLocalTailPacket.zeroRootResidual :=
  by
    change Core.Residual.residualOf rowElevenRun.value.previous =
      HypostructurePDEExamples.RepresentedNS2DLocalTailPacket.zeroRootResidual
    rw [rowEleven_retains_literal_row_ten]
    exact rowTen_retains_root_residual

#print axioms rowEleven_skips_inactive_payload
#print axioms rowEleven_work_is_bounded

end

end HypostructurePDEExamples.RepresentedNS2DConservativeCarrierPacket
