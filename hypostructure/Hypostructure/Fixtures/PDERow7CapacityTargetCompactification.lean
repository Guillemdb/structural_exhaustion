import Hypostructure.Fixtures.PDERow6FiniteOrthogonalAlignment
import Hypostructure.PDE.Contract

/-!
# PDE row-7 capacity and target-compactification fixture

This finite fixture exercises the generic row-7 executor on an active row-6
capacity-ready predecessor.  The same residual-owned CT14 capacity family is
used in two CT1 compactified-target schedules: an empty target schedule, which
routes to zero-capacity exclusion, and a singleton realized target schedule,
which routes to the positive-capacity witness residual.
-/

namespace Hypostructure.Fixtures.PDERow7CapacityTargetCompactification

open Hypostructure
open Hypostructure.Core
open Hypostructure.Core.Residual
open Hypostructure.PDE.FastTrack

noncomputable section

abbrev RowSixProfile :=
  PDERow6FiniteOrthogonalAlignment.positiveProfile.toRaw

abbrev RowSixStage :=
  CapacityProfile.RowSixStage RowSixProfile

abbrev CapacityView :=
  CapacityProfile.ActiveView RowSixProfile

def rowSixStage : RowSixStage :=
  PDERow6FiniteOrthogonalAlignment.positiveRun.value

def rowSixActive :
    RowSixProfile.CapacityReadyFocus.Active rowSixStage :=
  PDERow6FiniteOrthogonalAlignment.positiveCapacityReadyActive

def capacityView : CapacityView :=
  Focus.ActiveView.of rowSixStage rowSixActive

def memberSchedule : Core.Finite.Enumeration (Fin 1) :=
  Core.Finite.Enumeration.singleton 0

def viewQuery : Residual.Query CapacityView fun _view => CapacityView :=
  Residual.Query.residual

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

inductive TargetMode where
  | zero
  | positive
  deriving DecidableEq, Repr

abbrev TargetPrevious :=
  CT14.Stage capacitySpec capacityCapability

def targetSchedule : TargetMode -> Core.Finite.Enumeration Unit
  | .zero => Core.Finite.Enumeration.empty Unit
  | .positive => Core.Finite.Enumeration.singleton ()

def targetQuery (mode : TargetMode) :
    Residual.Query TargetPrevious fun _previous =>
      Core.Finite.Enumeration Unit :=
  Residual.Query.residual.map fun _previous _root => targetSchedule mode

def targetSpec (mode : TargetMode) : CT1.Spec TargetPrevious where
  Candidate := fun _previous => Unit
  Realizes := fun _previous _candidate => mode = .positive

def targetCapability (mode : TargetMode) :
    CT1.Capability (targetSpec mode) where
  schedule := targetQuery mode
  realizesDecidable := fun _previous _candidate => by
    change Decidable (mode = TargetMode.positive)
    infer_instance
  inputSize := fun _previous => 0
  workCoefficient := 1
  workDegree := 0
  workBound := by
    intro _previous
    cases mode <;>
      simp [CT1.searchCheckBound, targetQuery, targetSchedule,
        Core.Finite.Enumeration.card]
    · exact Nat.zero_le 1
    · exact Nat.le_refl 1

def contract (mode : TargetMode) :
    PDE.Contract.CapacityTarget RowSixProfile :=
  PDE.Contract.CapacityTarget.ofCapabilityCanonicalEnvelope
    capacitySpec capacityCapability (targetSpec mode) (targetCapability mode)

abbrev profile (mode : TargetMode) :
    CapacityProfile.Profile RowSixProfile :=
  (contract mode).toCapacityProfile

def zeroRun :=
  (contract .zero).run rowSixStage

def positiveRun :=
  (contract .positive).run rowSixStage

theorem runs_retain_literal_row_six :
    zeroRun.value.previous = rowSixStage /\
      positiveRun.value.previous = rowSixStage := by
  exact ⟨(contract .zero).run_previous rowSixStage,
    (contract .positive).run_previous rowSixStage⟩

theorem exact_active_work :
    zeroRun.checks =
      RowSixProfile.CapacityReadyFocus.selectionBudget.checks rowSixStage +
        (CapacityProfile.generateActiveCounted
          (profile .zero) capacityView).checks /\
    positiveRun.checks =
      RowSixProfile.CapacityReadyFocus.selectionBudget.checks rowSixStage +
        (CapacityProfile.generateActiveCounted
          (profile .positive) capacityView).checks := by
  exact ⟨(contract .zero).run_checks_of_active rowSixStage rowSixActive,
    (contract .positive).run_checks_of_active rowSixStage rowSixActive⟩

theorem runs_are_bounded :
    zeroRun.checks <=
      (RowSixProfile.CapacityReadyFocus.selectionBudget.add
        (CapacityProfile.payloadBudget (profile .zero))).coefficient *
      ((RowSixProfile.CapacityReadyFocus.selectionBudget.add
        (CapacityProfile.payloadBudget (profile .zero))).size rowSixStage + 1) ^
      (RowSixProfile.CapacityReadyFocus.selectionBudget.add
        (CapacityProfile.payloadBudget (profile .zero))).degree /\
    positiveRun.checks <=
      (RowSixProfile.CapacityReadyFocus.selectionBudget.add
        (CapacityProfile.payloadBudget (profile .positive))).coefficient *
      ((RowSixProfile.CapacityReadyFocus.selectionBudget.add
        (CapacityProfile.payloadBudget (profile .positive))).size rowSixStage + 1) ^
      (RowSixProfile.CapacityReadyFocus.selectionBudget.add
        (CapacityProfile.payloadBudget (profile .positive))).degree := by
  exact ⟨(contract .zero).run_checks_bounded rowSixStage,
    (contract .positive).run_checks_bounded rowSixStage⟩

def zeroStageActive :
    (CapacityProfile.SuccessorFocus (profile .zero)).Active zeroRun.value :=
  (contract .zero).runActiveProof rowSixStage rowSixActive

def positiveStageActive :
    (CapacityProfile.SuccessorFocus (profile .positive)).Active
      positiveRun.value :=
  (contract .positive).runActiveProof rowSixStage rowSixActive

def zeroOutput :=
  (CapacityProfile.outputQuery (profile .zero)).read zeroRun.value
    zeroStageActive

def positiveOutput :=
  (CapacityProfile.outputQuery (profile .positive)).read positiveRun.value
    positiveStageActive

theorem positiveOutput_terminal :
    positiveOutput.terminal = .c1 := by
  unfold positiveOutput positiveRun positiveStageActive
  rw [(contract .positive).outputQuery_run_of_active rowSixStage rowSixActive]
  apply CT1.ExecutionResult.terminal_c1_of_target
  refine ⟨(), ?_, rfl⟩
  change () ∈ [()]
  exact List.mem_singleton.mpr rfl

#print axioms runs_are_bounded

end

end Hypostructure.Fixtures.PDERow7CapacityTargetCompactification
