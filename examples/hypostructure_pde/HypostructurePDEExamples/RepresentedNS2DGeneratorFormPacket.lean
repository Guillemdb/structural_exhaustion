import Hypostructure.PDE.GeneratorForm
import HypostructurePDEExamples.RepresentedNS2DLocalTailPacket

/-!
# Represented 2D Navier--Stokes generator/form packet

This row-2 packet extends the represented zero-state registration from row 1
with a one-dimensional finite generator coordinate.  Every coordinate realizes
the same already-validated zero Navier--Stokes equation state.  The generator,
pairing, form, and all three decomposition terms are zero, so closedness,
generator representation, symmetry, skew-symmetry, nonnegativity, and the
sector estimate are proved algebraically for the declared finite topology.

The closed-form law below concerns only this represented zero-state packet.  It
does not assert closability of a Navier--Stokes operator, a Calderon--Zygmund
estimate, compactness, regularity, or any other analytic result.
-/

namespace HypostructurePDEExamples.RepresentedNS2DGeneratorFormPacket

open Hypostructure
open Hypostructure.PDE
open Hypostructure.PDE.NavierStokes
open HypostructurePDEExamples.RepresentedNS2DLocalTailPacket

noncomputable section

/-! ## Finite represented zero-state packet -/

/-- One real coordinate is the complete finite state space of this packet. -/
abbrev GeneratorState := Real

/-- Every finite coordinate realizes the row-1 represented zero equation. -/
def realizeState (_ : GeneratorState) :
    EquationState representedEquation workWindow :=
  zeroEquationState

theorem realized_state_is_zero (state : GeneratorState) :
    (realizeState state).object = zeroField 1 :=
  rfl

theorem realized_state_is_represented (state : GeneratorState) :
    RepresentedClassicalOn (realizeState state).object workWindow.region :=
  (realizeState state).valid

/-- The row-2 state carrier is attached to the literal represented row-1
equation on its registered work window. -/
def statePresentation : RepresentedStatePresentation model GeneratorState where
  window := workWindow
  realize := realizeState

/-! ## Generator form and its row-2 laws -/

/-- The sequential topology registered for the finite zero-form packet. -/
def finiteTopology : FormTopology GeneratorState where
  converges := fun sequence limit => sequence 0 = limit
  scalarCauchy := fun _ => True
  scalarConverges := fun sequence limit => sequence 0 = limit

/-- The zero bilinear form on the one-dimensional packet. -/
def zeroForm : BilinearForm GeneratorState := 0

/-- The zero form is closed for the explicitly registered finite topology. -/
def zeroClosedFormLaw :
    ClosedFormLaw GeneratorState (⊤ : Submodule Real GeneratorState)
      zeroForm finiteTopology where
  closed := by
    intro sequence limit inDomain converges formCauchy
    refine ⟨by simp, ?_⟩
    change (0 : Real) = 0
    rfl

/-- Row 2 specialized to the represented Navier--Stokes zero-state packet. -/
def generatorForm : GeneratorForm model GeneratorState where
  statePresentation := statePresentation
  domain := ⊤
  generator := 0
  pairing := zeroForm
  form := zeroForm
  symmetricPart := zeroForm
  skewPart := zeroForm
  boundaryPart := zeroForm
  topology := finiteTopology
  closure := .closed zeroClosedFormLaw
  generator_representation := by
    intro x hx y hy
    simp [zeroForm]
  decomposition := by
    intro x y
    simp [zeroForm]
  symmetric := by
    intro x y
    simp [zeroForm]
  skew := by
    intro x y
    simp [zeroForm]
  symmetric_nonnegative := by
    intro x hx
    simp [zeroForm]
  sectorConstant := 0
  sectorConstant_nonnegative := le_rfl
  sector := by
    intro x hx y hy
    simp [zeroForm]

/-- The exact row-2 ledger shape. -/
abbrev GeneratorFormStage :=
  Core.Residual.Ledger.Extension SignatureStage
    (fun _ => GeneratorForm model GeneratorState)

/-- Framework-owned row-2 registration on the literal row-1 stage. -/
def generatorFormStage : GeneratorFormStage :=
  generatorForm.register signatureStage

/-- Typed query for the form introduced by row 2. -/
def generatorFormQuery : Core.Residual.Query GeneratorFormStage
    (fun _ => GeneratorForm model GeneratorState) :=
  Core.Residual.Query.latest

theorem generator_form_stage_retains_row_one :
    generatorFormStage.previous = signatureStage :=
  GeneratorForm.register_previous generatorForm signatureStage

theorem generator_form_stage_retains_root_residual :
    Core.Residual.residualOf generatorFormStage = zeroRootResidual :=
  rfl

theorem registered_form_is_literal :
    generatorFormStage.added = generatorForm :=
  rfl

theorem registered_form_realizes_row_one_state (state : GeneratorState) :
    generatorForm.equationState state = realizeState state :=
  rfl

theorem registered_closed_form_law
    (sequence : Nat -> GeneratorState) (limit : GeneratorState)
    (inDomain : forall n, sequence n ∈ generatorForm.domain)
    (converges : generatorForm.topology.converges sequence limit)
    (formCauchy : generatorForm.topology.scalarCauchy
      (fun n => generatorForm.form (sequence n) (sequence n))) :
    limit ∈ generatorForm.domain /\
      generatorForm.topology.scalarConverges
        (fun n => generatorForm.form (sequence n) (sequence n))
        (generatorForm.form limit limit) :=
  zeroClosedFormLaw.closed sequence limit inDomain converges formCauchy

theorem registered_generator_representation (x y : GeneratorState) :
    generatorForm.form x y =
      generatorForm.pairing (generatorForm.generator x) y :=
  generatorForm.generator_representation x (by simp [generatorForm]) y
    (by simp [generatorForm])

theorem registered_decomposition (x y : GeneratorState) :
    generatorForm.form x y =
      generatorForm.symmetricPart x y + generatorForm.skewPart x y +
        generatorForm.boundaryPart x y :=
  generatorForm.decomposition x y

theorem registered_symmetric_law (x y : GeneratorState) :
    generatorForm.symmetricPart x y = generatorForm.symmetricPart y x :=
  generatorForm.symmetric x y

theorem registered_skew_law (x y : GeneratorState) :
    generatorForm.skewPart x y = -generatorForm.skewPart y x :=
  generatorForm.skew x y

theorem registered_symmetric_nonnegative (x : GeneratorState) :
    0 <= generatorForm.symmetricPart x x :=
  generatorForm.symmetric_nonnegative x (by simp [generatorForm])

theorem registered_sector_law (x y : GeneratorState) :
    abs (generatorForm.skewPart x y) <=
      generatorForm.sectorConstant *
        Real.sqrt (generatorForm.symmetricPart x x) *
        Real.sqrt (generatorForm.symmetricPart y y) :=
  generatorForm.sector x (by simp [generatorForm]) y
    (by simp [generatorForm])

/-! ## Explicit analytic boundary -/

/-- This finite algebraic row imports no analytic contract. -/
def importedAnalyticContracts : List Core.AuthorPrimitiveRef := []

theorem imported_analytic_boundary_is_empty :
    importedAnalyticContracts = [] :=
  rfl

#print axioms realized_state_is_represented
#print axioms generator_form_stage_retains_row_one
#print axioms generator_form_stage_retains_root_residual
#print axioms registered_form_realizes_row_one_state
#print axioms registered_closed_form_law
#print axioms registered_generator_representation
#print axioms registered_decomposition
#print axioms registered_symmetric_law
#print axioms registered_skew_law
#print axioms registered_symmetric_nonnegative
#print axioms registered_sector_law
#print axioms imported_analytic_boundary_is_empty

end

end HypostructurePDEExamples.RepresentedNS2DGeneratorFormPacket
