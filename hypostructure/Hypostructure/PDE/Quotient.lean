import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.Topology.Algebra.Module.ClosedSubmodule
import Hypostructure.Core.Residual.Focus
import Hypostructure.PDE.GeneratorForm

/-!
# Represented quotients and framework-computed defects

Applications register a projection, lift, and quotient generator.  The
intertwining defect is definitionally computed as `L_X U - U L_Q`; it is never
an application output.  Geometry classification uses Core's binary residual
decision on the exact defect stage.
-/

namespace Hypostructure.PDE

universe u v w uPrevious

/-- A represented quotient of the exact state carrier registered at row 2.

The quotient does not ask applications for a second `Ambient -> State`
handoff.  Its source is definitionally the carrier presented by `form`, so the
row-4 operator data cannot detach from the represented equation state. -/
structure RepresentedQuotient {M : LocalModel.{u}} {State : Type v}
    [AddCommGroup State] [Module Real State]
    (form : GeneratorForm M State) (Quotient : Type w)
    [AddCommGroup Quotient] [Module Real Quotient] where
  project : State →ₗ[Real] Quotient
  lift : Quotient →ₗ[Real] State
  project_lift : project.comp lift = LinearMap.id

/-- Primitive quotient generator on the quotient carrier.  The source
generator is recovered from the registered form through the row-4 query. -/
structure QuotientGenerator {M : LocalModel.{u}} {State : Type v}
    [AddCommGroup State] [Module Real State]
    (form : GeneratorForm M State)
    {Quotient : Type w} [AddCommGroup Quotient] [Module Real Quotient]
    (quotient : RepresentedQuotient form Quotient) where
  generator : Quotient →ₗ[Real] Quotient

/-- Framework-owned exact intertwining defect `L_X U - U L_Q`. -/
def intertwiningDefect {M : LocalModel.{u}} {State : Type v}
    [AddCommGroup State] [Module Real State]
    (form : GeneratorForm M State)
    {Quotient : Type w} [AddCommGroup Quotient] [Module Real Quotient]
    (quotient : RepresentedQuotient form Quotient)
    (quotientGenerator : QuotientGenerator form quotient) :
    Quotient →ₗ[Real] State :=
  form.generator.comp quotient.lift -
    quotient.lift.comp quotientGenerator.generator

@[simp]
theorem intertwiningDefect_apply {M : LocalModel.{u}} {State : Type v}
    [AddCommGroup State] [Module Real State]
    (form : GeneratorForm M State)
    {Quotient : Type w} [AddCommGroup Quotient] [Module Real Quotient]
    (quotient : RepresentedQuotient form Quotient)
    (quotientGenerator : QuotientGenerator form quotient)
    (value : Quotient) :
    intertwiningDefect form quotient quotientGenerator value =
      form.generator (quotient.lift value) -
        quotient.lift (quotientGenerator.generator value) :=
  rfl

/-- The bounded-operator presentation of a represented defect geometry.
`IsPositive` already contains symmetry and nonnegative quadratic-form
evidence; completeness promotes symmetry to Mathlib self-adjointness. -/
structure BoundedPositiveDefectGeometry (State : Type v)
    [NormedAddCommGroup State] [InnerProductSpace Real State]
    [CompleteSpace State] (carrier : ClosedSubmodule Real State) where
  operator : State →L[Real] State
  operator_positive : operator.IsPositive
  carrier_invariant : forall state, state ∈ carrier ->
    operator state ∈ carrier

/-- A closed symmetric-form presentation on an explicit complete form
domain.  The norm identity records that the supplied complete domain norm is
the form norm, rather than silently treating an ambient algebraic submodule as
closed. -/
structure ClosedSymmetricFormDefectGeometry
    (State : Type v) (Domain : Type v)
    [NormedAddCommGroup State] [InnerProductSpace Real State]
    [CompleteSpace State]
    [NormedAddCommGroup Domain] [InnerProductSpace Real Domain]
    [CompleteSpace Domain] (carrier : ClosedSubmodule Real State) where
  embedding : Domain →L[Real] carrier.toSubmodule
  embedding_injective : Function.Injective embedding
  embedding_dense : DenseRange embedding
  form : Domain →L[Real] Domain →L[Real] Real
  form_positive : form.toBilinForm.IsPosSemidef
  form_norm_sq : forall state,
    ‖state‖ ^ 2 = ‖embedding state‖ ^ 2 + form state state

/-- The two legal represented presentations on one exact closed carrier. -/
inductive DefectGeometryPresentation (State : Type v)
    [NormedAddCommGroup State] [InnerProductSpace Real State]
    [CompleteSpace State] (carrier : ClosedSubmodule Real State) where
  | boundedOperator
      (geometry : BoundedPositiveDefectGeometry State carrier)
  | closedSymmetricForm {Domain : Type v}
      [NormedAddCommGroup Domain] [InnerProductSpace Real Domain]
      [CompleteSpace Domain]
      (geometry : ClosedSymmetricFormDefectGeometry State Domain carrier)

/-- A represented geometry consists of one closed carrier and one exact legal
operator/form presentation on that carrier. -/
structure DefectGeometry (State : Type v)
    [NormedAddCommGroup State] [InnerProductSpace Real State]
    [CompleteSpace State] where
  carrier : ClosedSubmodule Real State
  presentation : DefectGeometryPresentation State carrier

namespace DefectGeometry

/-- Exact harmonic/kernel predicate induced by the registered geometry.

For a bounded presentation this is the literal operator kernel. For a closed
form presentation it is a represented form-domain vector whose pairing with
every form-domain test vector vanishes. This definition exposes no spectral
projection or pseudoinverse; those remain analytic capabilities. -/
def IsHarmonic {State : Type v}
    [NormedAddCommGroup State] [InnerProductSpace Real State]
    [CompleteSpace State]
    (geometry : DefectGeometry State) (state : State) : Prop :=
  match geometry.presentation with
  | .boundedOperator bounded => bounded.operator state = 0
  | @DefectGeometryPresentation.closedSymmetricForm _ _ _ _ _ Domain
      instNormed instInner instComplete form =>
      let _ := instNormed
      let _ := instInner
      let _ := instComplete
      exists potential : Domain,
        (form.embedding potential : State) = state /\
          forall test, form.form potential test = 0

/-- Exact containment proposition for an already computed defect operator. -/
def Contains {State : Type v}
    [NormedAddCommGroup State] [InnerProductSpace Real State]
    [CompleteSpace State]
    (geometry : DefectGeometry State)
    {Quotient : Type w} [AddCommGroup Quotient] [Module Real Quotient]
    (defect : Quotient →ₗ[Real] State) : Prop :=
  forall value, defect value ∈ geometry.carrier

end DefectGeometry

/-- Complete row-4 registration generated from the exact predecessor query.

The constructor is private: an application can register primitive quotient
and geometry data, but only the framework can attach the computed
intertwining defect to those exact inputs. -/
structure QuotientDefectRegistration
    (M : LocalModel.{u}) (State : Type v) (Quotient : Type w)
    [NormedAddCommGroup State] [InnerProductSpace Real State]
    [CompleteSpace State]
    [AddCommGroup Quotient] [Module Real Quotient] where
  private mk ::
  form : GeneratorForm M State
  quotient : RepresentedQuotient form Quotient
  quotientGenerator : QuotientGenerator form quotient
  geometry : DefectGeometry State
  defect : Quotient →ₗ[Real] State
  computed : defect =
    intertwiningDefect form quotient quotientGenerator

namespace QuotientDefectRegistration

/-- Exact row-4 success proposition for the registered, computed defect. -/
def IsContained {M : LocalModel.{u}} {State : Type v} {Quotient : Type w}
    [NormedAddCommGroup State] [InnerProductSpace Real State]
    [CompleteSpace State]
    [AddCommGroup Quotient] [Module Real Quotient]
    (registration : QuotientDefectRegistration M State Quotient) : Prop :=
  registration.geometry.Contains registration.defect

end QuotientDefectRegistration

/-- The row-4 stage carries the complete framework-generated registration. -/
abbrev DefectStage (Previous : Sort uPrevious) (M : LocalModel.{u})
    (State : Type v) (Quotient : Type w)
    [NormedAddCommGroup State] [InnerProductSpace Real State]
    [CompleteSpace State]
    [AddCommGroup Quotient] [Module Real Quotient] :=
  Core.Residual.Ledger.Extension Previous
    (fun _ => QuotientDefectRegistration M State Quotient)

/-- Core node that reads the exact inherited row-2 form and computes, rather
than receives, the row-4 defect.  The dependent quotient inputs are indexed by
the value returned by that ledger query. -/
def defectRegistrationNode {Previous : Sort uPrevious}
    {M : LocalModel.{u}} {State : Type v}
    [NormedAddCommGroup State] [InnerProductSpace Real State]
    [CompleteSpace State]
    (form : Core.Residual.Query Previous
      (fun _previous => GeneratorForm M State))
    {Quotient : Type w} [AddCommGroup Quotient] [Module Real Quotient]
    (quotient : (previous : Previous) ->
      RepresentedQuotient (form.read previous) Quotient)
    (quotientGenerator : (previous : Previous) ->
      QuotientGenerator (form.read previous) (quotient previous))
    (geometry : Previous -> DefectGeometry State) :
    Core.Residual.StageNode Previous
      (fun _ => QuotientDefectRegistration M State Quotient) :=
  Core.Residual.StageNode.create fun previous =>
    .mk (form.read previous) (quotient previous)
      (quotientGenerator previous) (geometry previous)
      (intertwiningDefect (form.read previous) (quotient previous)
        (quotientGenerator previous)) rfl

/-- Compute and register the exact defect in the complete predecessor ledger. -/
def registerDefect {Previous : Sort uPrevious}
    {M : LocalModel.{u}} {State : Type v}
    [NormedAddCommGroup State] [InnerProductSpace Real State]
    [CompleteSpace State]
    (form : Core.Residual.Query Previous
      (fun _previous => GeneratorForm M State))
    {Quotient : Type w} [AddCommGroup Quotient] [Module Real Quotient]
    (quotient : (previous : Previous) ->
      RepresentedQuotient (form.read previous) Quotient)
    (quotientGenerator : (previous : Previous) ->
      QuotientGenerator (form.read previous) (quotient previous))
    (geometry : Previous -> DefectGeometry State)
    (previous : Previous) :=
  (defectRegistrationNode form quotient quotientGenerator geometry).run
    previous

/-- Typed query for the complete row-4 registration. -/
def defectRegistrationQuery {Previous : Sort uPrevious}
    {M : LocalModel.{u}} {State : Type v} {Quotient : Type w}
    [NormedAddCommGroup State] [InnerProductSpace Real State]
    [CompleteSpace State]
    [AddCommGroup Quotient] [Module Real Quotient] :
    Core.Residual.Query (DefectStage Previous M State Quotient)
      (fun _ => QuotientDefectRegistration M State Quotient) :=
  Core.Residual.Query.latest

/-- Typed query for only the framework-computed defect. -/
def defectQuery {Previous : Sort uPrevious}
    {M : LocalModel.{u}} {State : Type v} {Quotient : Type w}
    [NormedAddCommGroup State] [InnerProductSpace Real State]
    [CompleteSpace State]
    [AddCommGroup Quotient] [Module Real Quotient] :
    Core.Residual.Query (DefectStage Previous M State Quotient)
      (fun _ => Quotient →ₗ[Real] State) :=
  defectRegistrationQuery.map fun _ registration => registration.defect

/-- Register the exhaustive geometry predicate and its literal complement on
the exact computed-defect stage.  The caller supplies decidability, not a
branch constructor. -/
def geometryDecisionNode {Previous : Sort uPrevious}
    {M : LocalModel.{u}} {State : Type v} {Quotient : Type w}
    [NormedAddCommGroup State] [InnerProductSpace Real State]
    [CompleteSpace State]
    [AddCommGroup Quotient] [Module Real Quotient]
    (decideContained : forall stage :
      DefectStage Previous M State Quotient,
      Decidable stage.added.IsContained) :
    Core.Residual.Decision.Node
      (DefectStage Previous M State Quotient)
      (fun stage => stage.added.IsContained)
      (fun stage => Not stage.added.IsContained) :=
  Core.Residual.Decision.Node.complement
    (fun stage : DefectStage Previous M State Quotient =>
      stage.added.IsContained)
    decideContained

/-- The exact decision stage emitted after row-4 registration. -/
abbrev GeometryDecisionStage (Previous : Sort uPrevious)
    (M : LocalModel.{u}) (State : Type v) (Quotient : Type w)
    [NormedAddCommGroup State] [InnerProductSpace Real State]
    [CompleteSpace State]
    [AddCommGroup Quotient] [Module Real Quotient] :=
  Core.Residual.Decision.Stage
    (fun stage : DefectStage Previous M State Quotient =>
      stage.added.IsContained)
    (fun stage : DefectStage Previous M State Quotient =>
      Not stage.added.IsContained)

/-- Execute the row-4 geometry split through Core routing state. -/
def decideGeometry {Previous : Sort uPrevious}
    {M : LocalModel.{u}} {State : Type v} {Quotient : Type w}
    [NormedAddCommGroup State] [InnerProductSpace Real State]
    [CompleteSpace State]
    [AddCommGroup Quotient] [Module Real Quotient]
    (decideContained : forall stage :
      DefectStage Previous M State Quotient,
      Decidable stage.added.IsContained)
    (stage : DefectStage Previous M State Quotient) :=
  (geometryDecisionNode decideContained).run stage

/-- The complete row-4 registration remains queryable after the geometry
decision without copying it into the decision payload. -/
def defectRegistrationQueryAtDecision {Previous : Sort uPrevious}
    {M : LocalModel.{u}} {State : Type v} {Quotient : Type w}
    [NormedAddCommGroup State] [InnerProductSpace Real State]
    [CompleteSpace State]
    [AddCommGroup Quotient] [Module Real Quotient] :
    Core.Residual.Query (GeometryDecisionStage Previous M State Quotient)
      (fun _ => QuotientDefectRegistration M State Quotient) :=
  defectRegistrationQuery.preserve

/-- The computed defect remains queryable after the geometry decision. -/
def defectQueryAtDecision {Previous : Sort uPrevious}
    {M : LocalModel.{u}} {State : Type v} {Quotient : Type w}
    [NormedAddCommGroup State] [InnerProductSpace Real State]
    [CompleteSpace State]
    [AddCommGroup Quotient] [Module Real Quotient] :
    Core.Residual.Query (GeometryDecisionStage Previous M State Quotient)
      (fun _ => Quotient →ₗ[Real] State) :=
  defectQuery.preserve

/-- Framework focus selecting only row-4's contained-geometry constructor. -/
def containedFocus {Previous : Sort uPrevious}
    {M : LocalModel.{u}} {State : Type v} {Quotient : Type w}
    [NormedAddCommGroup State] [InnerProductSpace Real State]
    [CompleteSpace State]
    [AddCommGroup Quotient] [Module Real Quotient] :
    Core.Residual.Focus.Profile
      (GeometryDecisionStage Previous M State Quotient) :=
  Core.Residual.Focus.yes

/-- Active read of the complete row-4 registration on the successful branch. -/
def containedRegistrationQuery {Previous : Sort uPrevious}
    {M : LocalModel.{u}} {State : Type v} {Quotient : Type w}
    [NormedAddCommGroup State] [InnerProductSpace Real State]
    [CompleteSpace State]
    [AddCommGroup Quotient] [Module Real Quotient] :
    Core.Residual.Focus.ActiveQuery
      (containedFocus (Previous := Previous) (M := M)
        (State := State) (Quotient := Quotient))
      (fun _stage _active => QuotientDefectRegistration M State Quotient) :=
  Core.Residual.Focus.ActiveQuery.ofQuery defectRegistrationQueryAtDecision

/-- Active read of the exact computed defect on row-4's successful branch. -/
def containedDefectQuery {Previous : Sort uPrevious}
    {M : LocalModel.{u}} {State : Type v} {Quotient : Type w}
    [NormedAddCommGroup State] [InnerProductSpace Real State]
    [CompleteSpace State]
    [AddCommGroup Quotient] [Module Real Quotient] :
    Core.Residual.Focus.ActiveQuery
      (containedFocus (Previous := Previous) (M := M)
        (State := State) (Quotient := Quotient))
      (fun _stage _active => Quotient →ₗ[Real] State) :=
  Core.Residual.Focus.ActiveQuery.ofQuery defectQueryAtDecision

/-- Active read of the exact containment proof selected by Core. -/
def containedProofQuery {Previous : Sort uPrevious}
    {M : LocalModel.{u}} {State : Type v} {Quotient : Type w}
    [NormedAddCommGroup State] [InnerProductSpace Real State]
    [CompleteSpace State]
    [AddCommGroup Quotient] [Module Real Quotient] :
    Core.Residual.Focus.ActiveQuery
      (containedFocus (Previous := Previous) (M := M)
        (State := State) (Quotient := Quotient))
      (fun stage _active => stage.previous.added.IsContained) :=
  Core.Residual.Focus.yesProof

@[simp]
theorem registerDefect_previous {Previous : Sort uPrevious}
    {M : LocalModel.{u}} {State : Type v}
    [NormedAddCommGroup State] [InnerProductSpace Real State]
    [CompleteSpace State]
    (form : Core.Residual.Query Previous
      (fun _previous => GeneratorForm M State))
    {Quotient : Type w} [AddCommGroup Quotient] [Module Real Quotient]
    (quotient : (previous : Previous) ->
      RepresentedQuotient (form.read previous) Quotient)
    (quotientGenerator : (previous : Previous) ->
      QuotientGenerator (form.read previous) (quotient previous))
    (geometry : Previous -> DefectGeometry State)
    (previous : Previous) :
    (registerDefect form quotient quotientGenerator geometry previous).previous =
      previous :=
  rfl

@[simp]
theorem registerDefect_added {Previous : Sort uPrevious}
    {M : LocalModel.{u}} {State : Type v}
    [NormedAddCommGroup State] [InnerProductSpace Real State]
    [CompleteSpace State]
    (form : Core.Residual.Query Previous
      (fun _previous => GeneratorForm M State))
    {Quotient : Type w} [AddCommGroup Quotient] [Module Real Quotient]
    (quotient : (previous : Previous) ->
      RepresentedQuotient (form.read previous) Quotient)
    (quotientGenerator : (previous : Previous) ->
      QuotientGenerator (form.read previous) (quotient previous))
    (geometry : Previous -> DefectGeometry State)
    (previous : Previous) :
    (registerDefect form quotient quotientGenerator geometry previous).added.defect =
      intertwiningDefect (form.read previous) (quotient previous)
        (quotientGenerator previous) :=
  rfl

@[simp]
theorem registerDefect_added_geometry {Previous : Sort uPrevious}
    {M : LocalModel.{u}} {State : Type v}
    [NormedAddCommGroup State] [InnerProductSpace Real State]
    [CompleteSpace State]
    (form : Core.Residual.Query Previous
      (fun _previous => GeneratorForm M State))
    {Quotient : Type w} [AddCommGroup Quotient] [Module Real Quotient]
    (quotient : (previous : Previous) ->
      RepresentedQuotient (form.read previous) Quotient)
    (quotientGenerator : (previous : Previous) ->
      QuotientGenerator (form.read previous) (quotient previous))
    (geometry : Previous -> DefectGeometry State)
    (previous : Previous) :
    (registerDefect form quotient quotientGenerator geometry previous).added.geometry =
      geometry previous :=
  rfl

end Hypostructure.PDE
