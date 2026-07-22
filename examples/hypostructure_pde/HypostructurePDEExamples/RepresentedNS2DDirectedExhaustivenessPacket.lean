import Mathlib.Topology.Algebra.Module.FiniteDimension
import Hypostructure.PDE.FastTrack.DirectedExhaustiveness
import HypostructurePDEExamples.RepresentedNS2DQuotientDefectPacket

/-!
# Represented 2D Navier--Stokes directed-exhaustiveness packet

This row-5 packet focuses the contained constructor of the literal row-4
quotient-defect decision.  On that focus it registers the total identity
structural gradient on the one-dimensional represented state carrier and
proves its gap and closed range directly in the finite model.  One singleton
CT15 schedule then reaches the capacity-fitting full-rank terminal, and the
framework's mandatory analytic bridge returns the already proved finite gap.

The CT16 and class-closure capabilities are total registrations required by
the exhaustive row-5 executor, but the generated full-rank branch does not run
them.  This packet is only a finite routing and accounting example.  It proves
no continuum closed-range theorem, Navier--Stokes estimate, regularity result,
or global existence statement.
-/

namespace HypostructurePDEExamples.RepresentedNS2DDirectedExhaustivenessPacket

open Hypostructure
open Hypostructure.Core
open Hypostructure.PDE
open Hypostructure.PDE.FastTrack
open Hypostructure.PDE.NavierStokes
open HypostructurePDEExamples.RepresentedNS2DGeneratorFormPacket
open HypostructurePDEExamples.RepresentedNS2DResourceBudgetPacket
open HypostructurePDEExamples.RepresentedNS2DQuotientDefectPacket

noncomputable section

/-! ## Literal row-4 focus -/

abbrev RowFourStage :=
  GeometryDecisionStage ResourceBudgetStage model GeneratorState QuotientState

/-- The PDE layer's framework-owned focus on row 4's contained constructor. -/
def rowFourFocus : Core.Residual.Focus.Profile RowFourStage :=
  containedFocus

/-- The concrete represented row-4 execution lies on the focused constructor. -/
theorem rowFourActive : rowFourFocus.Active containedDecision := by
  change Core.Residual.Focus.YesActive containedDecision
  cases selected : containedDecision.added with
  | yesBranch proof =>
      exact ⟨proof, selected⟩
  | noBranch absent =>
      exact (absent matching_defect_is_in_declared_geometry).elim

abbrev ActiveRowFour := Core.Residual.Focus.ActiveView rowFourFocus

/-! ## Honest finite structural gradient -/

/-- The total identity partial linear map on the represented real coordinate. -/
def identityOperator : GeneratorState →ₗ.[Real] GeneratorState where
  domain := ⊤
  toFun := (⊤ : Submodule Real GeneratorState).subtype

@[simp]
theorem identityOperator_apply (potential : identityOperator.domain) :
    identityOperator potential = (potential : GeneratorState) :=
  rfl

/-- Closed and densely defined identity gradient in the finite model. -/
def finiteStructuralGradient :
    StructuralGradient GeneratorState GeneratorState where
  operator := identityOperator
  operator_closed := identityOperator.graph.closed_of_finiteDimensional
  domain_dense := by
    change Dense ((⊤ : Submodule Real GeneratorState) : Set GeneratorState)
    rw [Submodule.top_coe]
    exact dense_univ

theorem finiteStructuralGradient_range :
    finiteStructuralGradient.range = ⊤ := by
  ext current
  constructor
  · intro _member
    trivial
  · intro _member
    exact (finiteStructuralGradient.mem_range_iff current).mpr
      ⟨⟨current, Submodule.mem_top⟩, rfl⟩

/-- The gap is proved from the displayed identity operator, not from CT15. -/
def finiteStructuralGap :
    StructuralGradient.PositiveStructuralGap finiteStructuralGradient where
  gamma := 1
  gamma_pos := zero_lt_one
  poincare := by
    intro potential _orthogonal
    change ‖(potential : GeneratorState)‖ ^ 2 ≤
      (1 : Real)⁻¹ * ‖(potential : GeneratorState)‖ ^ 2
    simp

def finiteClosedRange :
    StructuralGradient.ClosedRangeCertificate finiteStructuralGradient where
  range_isClosed := by
    rw [finiteStructuralGradient_range]
    exact isClosed_univ

/-- Both directions of the criterion are explicit finite-dimensional proofs. -/
def finiteClosedRangeCriterion :
    StructuralGradient.ClosedRangeCriterion finiteStructuralGradient where
  closedRange_iff_positiveGap :=
    ⟨fun _closed => ⟨finiteStructuralGap⟩,
      fun _gap => finiteClosedRange⟩

/-- The gradient is read only under the exact contained row-4 proof. -/
def gradientQuery :
    Core.Residual.Focus.ActiveQuery rowFourFocus
      (fun _stage _active =>
        StructuralGradient GeneratorState GeneratorState) :=
  (containedDefectQuery
    (Previous := ResourceBudgetStage) (M := model)
    (State := GeneratorState) (Quotient := QuotientState)).map
      (fun _stage _active _registeredDefect => finiteStructuralGradient)

def closedRangeCriterionQuery :
    Core.Residual.Focus.ActiveQuery rowFourFocus
      (fun stage active =>
        StructuralGradient.ClosedRangeCriterion
          (gradientQuery.read stage active)) :=
  gradientQuery.map
    (fun _stage _active _gradient => finiteClosedRangeCriterion)

/-! ## Residual-owned finite schedules -/

def unitScheduleActiveQuery :
    Core.Residual.Focus.ActiveQuery rowFourFocus
      (fun _stage _active => Core.Finite.Enumeration Unit) :=
  gradientQuery.map fun _stage _active _gradient =>
    Core.Finite.Enumeration.singleton ()

def unitScheduleQuery :
    Core.Residual.Query ActiveRowFour
      (fun _view => Core.Finite.Enumeration Unit) :=
  unitScheduleActiveQuery.onView

def rankSpec : CT15.Spec ActiveRowFour where
  Coordinate := fun _view => Unit
  TargetDependent := fun _view _coordinate => False
  charge := fun _view _coordinate => 1
  capacity := fun _view => 1

def rankCapability : CT15.Capability rankSpec where
  coordinates := unitScheduleQuery
  targetDependentDecidable := fun _view _coordinate => isFalse id
  inputSize := fun _view => 1
  workCoefficient := 2
  workDegree := 1
  workBound := by
    intro _view
    change 3 ≤ 2 * (1 + 1) ^ 1
    norm_num

/-! ## Total CT16 registration for the complementary rank-drop route -/

def supportSpec : CT16.Spec ActiveRowFour where
  Coordinate := fun _view => Unit
  InSupport := fun _view _coordinate => True
  ClosedCode := fun _view => Unit
  closedCode := fun _view => ()
  targetCode := fun _view => ()

def closedCodeComputation : CT16.ClosedCodeComputation supportSpec where
  run := fun _view => Core.Counted.pure ()
  correct := by intros; rfl
  budget := Core.PolynomialCheckBudget.proofOnly ActiveRowFour
  checks_eq := by intros; rfl

def codeEqualityDecision : CT16.CodeEqualityDecision supportSpec :=
  CT16.CodeEqualityDecision.unitCost (fun _view => 1)
    (by
      intro _view
      change DecidableEq Unit
      infer_instance)

def supportCapability : CT16.Capability supportSpec where
  coordinates := unitScheduleQuery
  inSupportDecidable := fun _view _coordinate => isTrue trivial
  codeComputation := closedCodeComputation
  equalityDecision := codeEqualityDecision

/-! ## Target-complete unit quotient -/

def classClosure : Core.ClosureOperator Unit :=
  Core.ClosureOperator.identity Unit

def targetNull (_carrier : Unit) : Prop :=
  True

def closedClassLedger : Core.ClosedClassLedger classClosure targetNull where
  classes := Set.univ
  closed := rfl
  targetNull := by simp [targetNull]

def quotientUniversal :
    Core.QuotientUniversalProperty (fun _carrier : Unit => ()) where
  descend := fun map _compatible _quotientClass => map ()
  descend_project := by intros; rfl
  descend_unique := by
    intro Result map compatible candidate commutes quotientClass
    cases quotientClass
    exact commutes ()

def classQuotient : Core.LedgerQuotient closedClassLedger where
  Quotient := Unit
  project := fun _carrier => ()
  null := ()
  killsClosed := by intros; rfl
  universal := quotientUniversal

def classFamilyActiveQuery :
    Core.Residual.Focus.ActiveQuery rowFourFocus
      (fun _stage _active => Core.Finite.Enumeration Unit) :=
  gradientQuery.map fun _stage _active _gradient =>
    Core.Finite.Enumeration.singleton ()

def classLedgerActiveQuery :
    Core.Residual.Focus.ActiveQuery rowFourFocus
      (fun _stage _active => Core.ClosedClassLedger classClosure targetNull) :=
  gradientQuery.map fun _stage _active _gradient => closedClassLedger

def closureProfile :
    Core.NormalForm.ClassClosure.Profile ActiveRowFour where
  Carrier := Unit
  closure := classClosure
  TargetNull := targetNull
  family := classFamilyActiveQuery.onView
  ledger := classLedgerActiveQuery.onView
  quotient := fun _view => classQuotient
  TargetVisible := fun _view _quotientClass => False
  targetVisibleDecidable := fun _view _quotientClass => isFalse id
  visibleNonzero := by intros _view _carrier visible; exact visible.elim
  nullOfNotVisible := by intros; rfl
  targetNullOfNull := by simp [targetNull]
  closureStable := Core.ClosureStable.identity

def nextClassQuotient (view : ActiveRowFour)
    (avoids : closureProfile.AvoidsTargetVisible view) :
    Core.LedgerQuotient (closureProfile.extendedLedger view avoids) where
  Quotient := Unit
  project := fun _carrier => ()
  null := ()
  killsClosed := by intros; rfl
  universal := quotientUniversal

def closureRegistration :
    Core.NormalForm.ClassClosure.ExtensionRegistration closureProfile where
  nextQuotient := nextClassQuotient
  quotientTransport := fun _view _avoids _quotientClass => ()
  quotientTransport_project := by intros; rfl
  quotientTransport_null := by intros; rfl

def targetComplete :
    Core.NormalForm.ClassClosure.TargetComplete closureProfile where
  representsNonzero := by
    intro _view quotientClass nonzero
    exact (nonzero (by cases quotientClass; rfl)).elim

/-! ## Framework semantic bridges -/

/-- CT15's finite output does not prove the gap; both callbacks return the
independently verified identity-gradient gap above. -/
def fullRankToGap :
    DirectedExhaustiveness.FullRankToGap rowFourFocus gradientQuery
      rankSpec rankCapability where
  fromC4 := fun _view _output => finiteStructuralGap
  fromFullRankLedger := fun _view _output => finiteStructuralGap

def codeClosureAlignment :
    DirectedExhaustiveness.CodeClosureAlignment rowFourFocus rankSpec
      rankCapability supportSpec supportCapability closureProfile where
  properSupportImpossible := by
    intro _view _rankDrop properSupport
    exact properSupport.residual.absent trivial
  exactCodeAvoids := by
    intro _view _rankDrop _exactCode _index visible
    exact visible
  mismatchVisible := by
    intro view _rankDrop mismatch
    have equal : mismatch.residual.state.code =
        supportSpec.targetCode view := by
      exact mismatch.residual.state.exact.trans rfl
    exact (mismatch.residual.notEqual equal).elim

/-- Every hard row-5 bridge is read from the literal row-4 focused ledger. -/
def targetCompleteQuery :
    Core.Residual.Focus.ActiveQuery rowFourFocus
      (fun _stage _active =>
        Core.NormalForm.ClassClosure.TargetComplete closureProfile) :=
  gradientQuery.map fun _stage _active _gradient => targetComplete

def fullRankToGapQuery :
    Core.Residual.Focus.ActiveQuery rowFourFocus
      (fun _stage _active =>
        DirectedExhaustiveness.FullRankToGap rowFourFocus gradientQuery
          rankSpec rankCapability) :=
  gradientQuery.map fun _stage _active _gradient => fullRankToGap

def codeClosureAlignmentQuery :
    Core.Residual.Focus.ActiveQuery rowFourFocus
      (fun _stage _active =>
        DirectedExhaustiveness.CodeClosureAlignment rowFourFocus rankSpec
          rankCapability supportSpec supportCapability closureProfile) :=
  gradientQuery.map fun _stage _active _gradient => codeClosureAlignment

def rowFiveProfile :
    DirectedExhaustiveness.Profile RowFourStage rowFourFocus
      GeneratorState GeneratorState where
  gradient := gradientQuery
  closedRangeCriterion := closedRangeCriterionQuery
  rankSpec := rankSpec
  rankCapability := rankCapability
  supportSpec := supportSpec
  supportCapability := supportCapability
  closureProfile := closureProfile
  closureRegistration := closureRegistration
  targetComplete := targetCompleteQuery
  InWindow := fun _view _carrier => True
  targetCapacity := fun _view _carrier => 1
  targetFlux := fun _view _carrier => 1
  inWindowOfVisible := by intros; trivial
  positiveCapacityOfVisible := by intros; norm_num
  nonzeroFluxOfVisible := by intros; norm_num
  fullRankToGap := fullRankToGapQuery
  codeClosureAlignment := codeClosureAlignmentQuery

/-! ## One row-5 stage and its audit surface -/

abbrev RowFiveOutput (previous : RowFourStage)
    (active : rowFourFocus.Active previous) :=
  DirectedExhaustiveness.Output rowFiveProfile previous active

abbrev RowFiveStage :=
  DirectedExhaustiveness.Stage rowFiveProfile

abbrev RowFiveSuccessorFocus :=
  rowFiveProfile.SuccessorFocus

/-- The sole row-5 execution, appended to the literal row-4 decision stage. -/
def rowFiveRun : Core.Counted RowFiveStage :=
  DirectedExhaustiveness.run rowFiveProfile containedDecision

def rowFiveStage : RowFiveStage :=
  rowFiveRun.value

theorem rowFiveStage_retains_rowFour :
    rowFiveStage.previous = containedDecision :=
  DirectedExhaustiveness.run_previous rowFiveProfile containedDecision

theorem rowFiveStage_retains_root_residual :
    Core.Residual.residualOf rowFiveStage =
      HypostructurePDEExamples.RepresentedNS2DLocalTailPacket.zeroRootResidual :=
  by
    change Core.Residual.residualOf rowFiveStage.previous =
      HypostructurePDEExamples.RepresentedNS2DLocalTailPacket.zeroRootResidual
    rw [rowFiveStage_retains_rowFour]
    change Core.Residual.residualOf containedDecision.previous =
      HypostructurePDEExamples.RepresentedNS2DLocalTailPacket.zeroRootResidual
    rw [contained_decision_retains_computed_stage]
    exact zero_defect_stage_retains_root_residual

/-- The framework successor focus still selects the same row-4 constructor. -/
theorem rowFiveStageActive : RowFiveSuccessorFocus.Active rowFiveStage := by
  change rowFourFocus.Active rowFiveStage.previous
  rw [rowFiveStage_retains_rowFour]
  exact rowFourActive

/-- Read the generated payload through row 5's public accumulated-ledger
query, rather than by inspecting the focus outcome constructor. -/
def rowFiveOutputFromLedger :
    DirectedExhaustiveness.Output rowFiveProfile rowFiveStage.previous
      rowFiveStageActive :=
  rowFiveProfile.outputQuery.read rowFiveStage rowFiveStageActive

/-- Exact branch-sensitive work: one Core focus selection plus exactly the
payload schedule registered by the row-5 executor. -/
theorem rowFiveRun_exact_work :
    rowFiveRun.checks =
      rowFourFocus.selectionBudget.checks containedDecision +
        (DirectedExhaustiveness.payloadBudget rowFiveProfile).checks
          containedDecision :=
  DirectedExhaustiveness.run_checks_of_active rowFiveProfile
    containedDecision rowFourActive

theorem rowFiveRun_work_is_bounded :
    rowFiveRun.checks ≤
      (rowFourFocus.selectionBudget.add
        (DirectedExhaustiveness.payloadBudget rowFiveProfile)).coefficient *
      ((rowFourFocus.selectionBudget.add
        (DirectedExhaustiveness.payloadBudget rowFiveProfile)).size
          containedDecision + 1) ^
      (rowFourFocus.selectionBudget.add
        (DirectedExhaustiveness.payloadBudget rowFiveProfile)).degree :=
  DirectedExhaustiveness.run_checks_bounded rowFiveProfile containedDecision

/-- The active payload itself follows the finite full-rank route. -/
theorem activePayload_is_positiveGap :
    (DirectedExhaustiveness.generateActive rowFiveProfile
      (Core.Residual.Focus.ActiveView.of containedDecision rowFourActive)).terminal =
        .positiveStructuralGap := by
  rfl

def activePositiveGapOutput :
    DirectedExhaustiveness.PositiveGapOutput rowFiveProfile
      (Core.Residual.Focus.ActiveView.of containedDecision rowFourActive) :=
  (DirectedExhaustiveness.generateActive rowFiveProfile
    (Core.Residual.Focus.ActiveView.of containedDecision rowFourActive)).positiveGapOutput
      activePayload_is_positiveGap

theorem activeOutput_has_closed_range :
    StructuralGradient.ClosedRangeCertificate finiteStructuralGradient :=
  activePositiveGapOutput.closedRange

def activeOutputDirectedExhaustiveness :
    StructuralGradient.DirectedExhaustivenessCertificate
      finiteStructuralGradient :=
  activePositiveGapOutput.directed

/-! ## Explicit trust boundary -/

/-- This represented finite packet imports no analytic author primitive. -/
def importedAnalyticContracts : List Core.AuthorPrimitiveRef := []

theorem imported_analytic_boundary_is_empty :
    importedAnalyticContracts = [] :=
  rfl

#print axioms finiteStructuralGap
#print axioms finiteClosedRangeCriterion
#print axioms rowFiveStage
#print axioms rowFiveStage_retains_rowFour
#print axioms rowFiveStage_retains_root_residual
#print axioms rowFiveOutputFromLedger
#print axioms rowFiveRun_exact_work
#print axioms rowFiveRun_work_is_bounded
#print axioms activePayload_is_positiveGap
#print axioms activeOutputDirectedExhaustiveness
#print axioms imported_analytic_boundary_is_empty

end

end HypostructurePDEExamples.RepresentedNS2DDirectedExhaustivenessPacket
