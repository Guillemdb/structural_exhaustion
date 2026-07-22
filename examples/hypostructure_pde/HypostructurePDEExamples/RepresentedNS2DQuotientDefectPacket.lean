import Hypostructure.PDE.Quotient
import HypostructurePDEExamples.RepresentedNS2DResourceBudgetPacket

/-!
# Represented 2D Navier--Stokes quotient-defect packet

This row-4 packet extends the literal row-3 resource stage.  Its represented
quotient is the identity quotient of the row-2 finite state carrier.  The PDE
framework computes the intertwining defect from the registered generators and
uses Core's exhaustive decision to test membership in one declared geometry.

The matching generator produces the zero defect and the mismatched generator
produces a nonzero complementary residual.  Both are finite algebraic fixture
executions.  This file proves no continuum quotient theorem, defect estimate,
closed-range theorem, or Navier--Stokes regularity statement.
-/

namespace HypostructurePDEExamples.RepresentedNS2DQuotientDefectPacket

open Hypostructure
open Hypostructure.PDE
open Hypostructure.PDE.NavierStokes
open HypostructurePDEExamples.RepresentedNS2DGeneratorFormPacket
open HypostructurePDEExamples.RepresentedNS2DLocalTailPacket
open HypostructurePDEExamples.RepresentedNS2DResourceBudgetPacket

noncomputable section

universe uPrevious

/-! ## Row-2-owned represented quotient -/

/-- The quotient carrier is the exact finite state carrier registered at row
2, not a second ambient representation. -/
abbrev QuotientState := GeneratorState

/-- Identity quotient of the represented generator state. -/
def representedQuotient (form : GeneratorForm model GeneratorState) :
    RepresentedQuotient form QuotientState where
  project := LinearMap.id
  lift := LinearMap.id
  project_lift := by
    apply LinearMap.ext
    intro value
    rfl

theorem quotient_lift_realizes_registered_equation (value : QuotientState) :
    generatorForm.equationState
        ((representedQuotient generatorForm).lift value) =
      realizeState value :=
  rfl

/-! ## Framework-computed defects -/

/-- The quotient generator matching the registered zero generator. -/
def matchingQuotientGenerator
    (form : GeneratorForm model GeneratorState) :
    QuotientGenerator form (representedQuotient form) where
  generator := 0

/-- A finite complementary fixture whose quotient generator is the identity. -/
def mismatchedQuotientGenerator
    (form : GeneratorForm model GeneratorState) :
    QuotientGenerator form (representedQuotient form) where
  generator := LinearMap.id

/-- The only inherited row-2 datum used by row 4, retrieved through row 3. -/
def formQuery : Core.Residual.Query ResourceBudgetStage
    (fun _ => GeneratorForm model GeneratorState) :=
  generatorFormQueryAtRowThree

def quotientAt (previous : ResourceBudgetStage) :
    RepresentedQuotient (formQuery.read previous) QuotientState :=
  representedQuotient (formQuery.read previous)

def matchingGeneratorAt (previous : ResourceBudgetStage) :
    QuotientGenerator (formQuery.read previous) (quotientAt previous) :=
  matchingQuotientGenerator (formQuery.read previous)

def mismatchedGeneratorAt (previous : ResourceBudgetStage) :
    QuotientGenerator (formQuery.read previous) (quotientAt previous) :=
  mismatchedQuotientGenerator (formQuery.read previous)

/-! ## Declared defect geometry -/

/-- The declared geometry contains exactly the zero defect. -/
def zeroDefectGeometry : DefectGeometry GeneratorState where
  carrier := ⊥
  presentation := .boundedOperator {
    operator := 0
    operator_positive := ContinuousLinearMap.isPositive_zero
    carrier_invariant := by
      intro state inCarrier
      simp
  }

/-- Exact row-4 registration on the literal row-3 stage. -/
def zeroDefectStage :=
  registerDefect formQuery quotientAt matchingGeneratorAt
    (fun _ => zeroDefectGeometry) resourceBudgetStage

/-- The same row-4 executor with data whose computed defect is nonzero. -/
def nonzeroDefectStage :=
  registerDefect formQuery quotientAt mismatchedGeneratorAt
    (fun _ => zeroDefectGeometry) resourceBudgetStage

theorem zero_defect_stage_retains_row_three :
    zeroDefectStage.previous = resourceBudgetStage :=
  registerDefect_previous formQuery quotientAt matchingGeneratorAt
    (fun _ => zeroDefectGeometry)
    resourceBudgetStage

theorem nonzero_defect_stage_retains_row_three :
    nonzeroDefectStage.previous = resourceBudgetStage :=
  registerDefect_previous formQuery quotientAt mismatchedGeneratorAt
    (fun _ => zeroDefectGeometry)
    resourceBudgetStage

theorem zero_defect_stage_retains_root_residual :
    Core.Residual.residualOf zeroDefectStage = zeroRootResidual :=
  rfl

theorem nonzero_defect_stage_retains_root_residual :
    Core.Residual.residualOf nonzeroDefectStage = zeroRootResidual :=
  rfl

theorem computed_matching_defect_is_zero :
    zeroDefectStage.added.defect = 0 := by
  apply LinearMap.ext
  intro value
  change intertwiningDefect generatorForm
    (representedQuotient generatorForm)
      (matchingQuotientGenerator generatorForm) value = 0
  simp [intertwiningDefect, matchingQuotientGenerator,
    representedQuotient, generatorForm]

theorem computed_mismatched_defect_is_negative_identity :
    nonzeroDefectStage.added.defect =
      -(LinearMap.id : QuotientState →ₗ[Real] GeneratorState) := by
  apply LinearMap.ext
  intro value
  change intertwiningDefect generatorForm
    (representedQuotient generatorForm)
      (mismatchedQuotientGenerator generatorForm) value = -value
  simp [intertwiningDefect, mismatchedQuotientGenerator,
    representedQuotient, generatorForm]

theorem computed_mismatched_defect_at_one :
    nonzeroDefectStage.added.defect 1 = -1 := by
  change intertwiningDefect generatorForm
    (representedQuotient generatorForm)
      (mismatchedQuotientGenerator generatorForm) 1 = -1
  simp [intertwiningDefect, mismatchedQuotientGenerator,
    representedQuotient, generatorForm]

/-! ## Exhaustive theorem-level geometry decision -/

noncomputable def geometryDecidable {Previous : Sort uPrevious} :
    forall stage : DefectStage Previous model GeneratorState QuotientState,
      Decidable stage.added.IsContained := by
  intro stage
  classical
  infer_instance

noncomputable def containedDecision :=
  decideGeometry geometryDecidable zeroDefectStage

noncomputable def complementaryDecision :=
  decideGeometry geometryDecidable nonzeroDefectStage

theorem matching_defect_is_in_declared_geometry :
    zeroDefectGeometry.Contains zeroDefectStage.added.defect := by
  intro value
  rw [computed_matching_defect_is_zero]
  simp [zeroDefectGeometry]

theorem mismatched_defect_is_outside_declared_geometry :
    Not (zeroDefectGeometry.Contains nonzeroDefectStage.added.defect) := by
  intro contained
  have atOne := contained 1
  have isZero : nonzeroDefectStage.added.defect 1 = 0 := by
    simpa [zeroDefectGeometry] using atOne
  rw [computed_mismatched_defect_at_one] at isZero
  norm_num at isZero

theorem contained_decision_uses_success_branch :
    match containedDecision.added with
    | .yesBranch _ => True
    | .noBranch _ => False := by
  cases h : containedDecision.added with
  | yesBranch proof => trivial
  | noBranch absent =>
      exact (absent matching_defect_is_in_declared_geometry).elim

theorem complementary_decision_uses_residual_branch :
    match complementaryDecision.added with
    | .yesBranch _ => False
    | .noBranch _ => True := by
  cases h : complementaryDecision.added with
  | yesBranch contained =>
      exact (mismatched_defect_is_outside_declared_geometry contained).elim
  | noBranch absent => trivial

theorem contained_decision_retains_computed_stage :
    containedDecision.previous = zeroDefectStage :=
  rfl

theorem complementary_decision_retains_computed_stage :
    complementaryDecision.previous = nonzeroDefectStage :=
  rfl

/-! ## Explicit analytic boundary -/

/-- Row 4 imports no continuum quotient or defect estimate. -/
def importedAnalyticContracts : List Core.AuthorPrimitiveRef := []

theorem no_imported_continuum_quotient_contract :
    importedAnalyticContracts = [] :=
  rfl

#print axioms quotient_lift_realizes_registered_equation
#print axioms zero_defect_stage_retains_row_three
#print axioms nonzero_defect_stage_retains_row_three
#print axioms zero_defect_stage_retains_root_residual
#print axioms nonzero_defect_stage_retains_root_residual
#print axioms computed_matching_defect_is_zero
#print axioms computed_mismatched_defect_is_negative_identity
#print axioms computed_mismatched_defect_at_one
#print axioms matching_defect_is_in_declared_geometry
#print axioms mismatched_defect_is_outside_declared_geometry
#print axioms contained_decision_uses_success_branch
#print axioms complementary_decision_uses_residual_branch
#print axioms contained_decision_retains_computed_stage
#print axioms complementary_decision_retains_computed_stage
#print axioms no_imported_continuum_quotient_contract

end

end HypostructurePDEExamples.RepresentedNS2DQuotientDefectPacket
