import Hypostructure.Core.Residual.Decision
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

/-- A represented quotient whose public class is independent of the ambient
representative. -/
structure RepresentedQuotient (M : LocalModel.{u})
    (semantics : RepresentationSemantics M.problem)
    (State : Type v) (Quotient : Type w)
    [AddCommGroup State] [Module Real State]
    [AddCommGroup Quotient] [Module Real Quotient] where
  represent : M.problem.Ambient -> State
  project : State →ₗ[Real] Quotient
  lift : Quotient →ₗ[Real] State
  project_lift : project.comp lift = LinearMap.id
  equivalent_project : forall {left right},
    semantics.equivalent left right ->
      project (represent left) = project (represent right)

/-- Primitive quotient generator.  Its ambient counterpart is read from the
registered generator/form capability. -/
structure QuotientGenerator {M : LocalModel.{u}} {State : Type v}
    [AddCommGroup State] [Module Real State]
    (form : GeneratorForm M State)
    {semantics : RepresentationSemantics M.problem}
    {Quotient : Type w} [AddCommGroup Quotient] [Module Real Quotient]
    (quotient : RepresentedQuotient M semantics State Quotient) where
  generator : Quotient →ₗ[Real] Quotient

/-- Framework-owned exact intertwining defect `L_X U - U L_Q`. -/
def intertwiningDefect {M : LocalModel.{u}} {State : Type v}
    [AddCommGroup State] [Module Real State]
    (form : GeneratorForm M State)
    {semantics : RepresentationSemantics M.problem}
    {Quotient : Type w} [AddCommGroup Quotient] [Module Real Quotient]
    (quotient : RepresentedQuotient M semantics State Quotient)
    (quotientGenerator : QuotientGenerator form quotient) :
    Quotient →ₗ[Real] State :=
  form.generator.comp quotient.lift -
    quotient.lift.comp quotientGenerator.generator

@[simp]
theorem intertwiningDefect_apply {M : LocalModel.{u}} {State : Type v}
    [AddCommGroup State] [Module Real State]
    (form : GeneratorForm M State)
    {semantics : RepresentationSemantics M.problem}
    {Quotient : Type w} [AddCommGroup Quotient] [Module Real Quotient]
    (quotient : RepresentedQuotient M semantics State Quotient)
    (quotientGenerator : QuotientGenerator form quotient)
    (value : Quotient) :
    intertwiningDefect form quotient quotientGenerator value =
      form.generator (quotient.lift value) -
        quotient.lift (quotientGenerator.generator value) :=
  rfl

/-- Positive operator geometry in which a computed defect may be routed. -/
structure DefectGeometry (State : Type v)
    [AddCommGroup State] [Module Real State] where
  domain : Submodule Real State
  carrier : Submodule Real State
  carrier_le_domain : carrier <= domain
  pairing : BilinearForm State
  positiveOperator : State →ₗ[Real] State
  positive_on_domain : forall state, state ∈ domain ->
    0 <= pairing (positiveOperator state) state
  preserves_carrier : forall state, state ∈ carrier ->
    positiveOperator state ∈ carrier

/-- Exact containment proposition for an already computed defect operator. -/
def DefectGeometry.Contains {State : Type v}
    [AddCommGroup State] [Module Real State]
    (geometry : DefectGeometry State)
    {Quotient : Type w} [AddCommGroup Quotient] [Module Real Quotient]
    (defect : Quotient →ₗ[Real] State) : Prop :=
  forall value, defect value ∈ geometry.carrier

/-- The row-4 defect stage is just a generic ledger extension carrying the
framework-computed linear map. -/
abbrev DefectStage (Previous : Sort uPrevious)
    (State : Type v) (Quotient : Type w)
    [AddCommGroup State] [Module Real State]
    [AddCommGroup Quotient] [Module Real Quotient] :=
  Core.Residual.Ledger.Extension Previous
    (fun _ => Quotient →ₗ[Real] State)

/-- Core node that computes, rather than receives, the row-4 defect. -/
def defectRegistrationNode {Previous : Sort uPrevious}
    {M : LocalModel.{u}} {State : Type v}
    [AddCommGroup State] [Module Real State]
    (form : GeneratorForm M State)
    {semantics : RepresentationSemantics M.problem}
    {Quotient : Type w} [AddCommGroup Quotient] [Module Real Quotient]
    (quotient : RepresentedQuotient M semantics State Quotient)
    (quotientGenerator : QuotientGenerator form quotient) :
    Core.Residual.StageNode Previous
      (fun _ => Quotient →ₗ[Real] State) :=
  Core.Residual.StageNode.create fun _ =>
    intertwiningDefect form quotient quotientGenerator

/-- Compute and register the exact defect in the complete predecessor ledger. -/
def registerDefect {Previous : Sort uPrevious}
    {M : LocalModel.{u}} {State : Type v}
    [AddCommGroup State] [Module Real State]
    (form : GeneratorForm M State)
    {semantics : RepresentationSemantics M.problem}
    {Quotient : Type w} [AddCommGroup Quotient] [Module Real Quotient]
    (quotient : RepresentedQuotient M semantics State Quotient)
    (quotientGenerator : QuotientGenerator form quotient)
    (previous : Previous) :=
  (defectRegistrationNode form quotient quotientGenerator).run previous

/-- Register the exhaustive geometry predicate and its literal complement on
the exact computed-defect stage.  The caller supplies decidability, not a
branch constructor. -/
def geometryDecisionNode {Previous : Sort uPrevious}
    {State : Type v} {Quotient : Type w}
    [AddCommGroup State] [Module Real State]
    [AddCommGroup Quotient] [Module Real Quotient]
    (geometry : DefectGeometry State)
    (decideContained : forall stage : DefectStage Previous State Quotient,
      Decidable (geometry.Contains stage.added)) :
    Core.Residual.Decision.Node
      (DefectStage Previous State Quotient)
      (fun stage => geometry.Contains stage.added)
      (fun stage => Not (geometry.Contains stage.added)) :=
  Core.Residual.Decision.Node.complement
    (fun stage : DefectStage Previous State Quotient =>
      geometry.Contains stage.added)
    decideContained

/-- Execute the row-4 geometry split through Core routing state. -/
def decideGeometry {Previous : Sort uPrevious}
    {State : Type v} {Quotient : Type w}
    [AddCommGroup State] [Module Real State]
    [AddCommGroup Quotient] [Module Real Quotient]
    (geometry : DefectGeometry State)
    (decideContained : forall stage : DefectStage Previous State Quotient,
      Decidable (geometry.Contains stage.added))
    (stage : DefectStage Previous State Quotient) :=
  (geometryDecisionNode geometry decideContained).run stage

@[simp]
theorem registerDefect_previous {Previous : Sort uPrevious}
    {M : LocalModel.{u}} {State : Type v}
    [AddCommGroup State] [Module Real State]
    (form : GeneratorForm M State)
    {semantics : RepresentationSemantics M.problem}
    {Quotient : Type w} [AddCommGroup Quotient] [Module Real Quotient]
    (quotient : RepresentedQuotient M semantics State Quotient)
    (quotientGenerator : QuotientGenerator form quotient)
    (previous : Previous) :
    (registerDefect form quotient quotientGenerator previous).previous =
      previous :=
  rfl

end Hypostructure.PDE
