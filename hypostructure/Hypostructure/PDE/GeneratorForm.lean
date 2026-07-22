import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Hypostructure.PDE.FastTrack.Signature

/-!
# Generic represented generator forms

Row 2 registers primitive generator/form data on a represented local equation
state.  The capability uses a caller-registered sequential form topology, so
closedness and closability are explicit mathematical laws rather than hidden
analytic assumptions.
-/

namespace Hypostructure.PDE

universe u v uPrevious

/-- Real bilinear forms used by the generic continuum registration. -/
abbrev BilinearForm (State : Type v) [AddCommGroup State]
    [Module Real State] :=
  State →ₗ[Real] State →ₗ[Real] Real

/-- The convergence relations against which form closure is certified. -/
structure FormTopology (State : Type v) where
  converges : (Nat -> State) -> State -> Prop
  scalarCauchy : (Nat -> Real) -> Prop
  scalarConverges : (Nat -> Real) -> Real -> Prop

/-- Sequential closedness of a represented form on its declared domain. -/
structure ClosedFormLaw (State : Type v) [AddCommGroup State]
    [Module Real State] (domain : Submodule Real State)
    (form : BilinearForm State) (topology : FormTopology State) : Prop where
  closed : forall (sequence : Nat -> State) (limit : State),
    (forall n, sequence n ∈ domain) ->
    topology.converges sequence limit ->
    topology.scalarCauchy (fun n => form (sequence n) (sequence n)) ->
      limit ∈ domain /\
        topology.scalarConverges
          (fun n => form (sequence n) (sequence n)) (form limit limit)

/-- Sequential closability: a form-Cauchy sequence vanishing in the ambient
topology has vanishing form energy. -/
structure ClosableFormLaw (State : Type v) [AddCommGroup State]
    [Module Real State] (domain : Submodule Real State)
    (form : BilinearForm State) (topology : FormTopology State) : Prop where
  closesAtZero : forall (sequence : Nat -> State),
    (forall n, sequence n ∈ domain) ->
    topology.converges sequence 0 ->
    topology.scalarCauchy (fun n => form (sequence n) (sequence n)) ->
      topology.scalarConverges (fun n => form (sequence n) (sequence n)) 0

/-- Row 2 accepts either a closed represented form or a certified closable
form.  Later rows may separately register the chosen closure. -/
inductive FormClosureLaw (State : Type v) [AddCommGroup State]
    [Module Real State] (domain : Submodule Real State)
    (form : BilinearForm State) (topology : FormTopology State) : Prop
  | closed (law : ClosedFormLaw State domain form topology)
  | closable (law : ClosableFormLaw State domain form topology)

/-- A total presentation of generator states as valid represented equation
states on one fixed local window.  This is only a semantic attachment to the
registered equation; it supplies no analytic admissibility theorem. -/
structure RepresentedStatePresentation (M : LocalModel.{u})
    (State : Type v) where
  window : M.atlas.Window
  realize : State -> EquationState M.equation window

namespace RepresentedStatePresentation

/-- Restrict a represented generator state to any nested local window. -/
def restrict {M : LocalModel.{u}} {State : Type v}
    (presentation : RepresentedStatePresentation M State)
    {window : M.atlas.Window}
    (nested : M.atlas.nested window presentation.window)
    (state : State) : EquationState M.equation window :=
  (presentation.realize state).restrict nested

@[simp]
theorem restrict_object {M : LocalModel.{u}} {State : Type v}
    (presentation : RepresentedStatePresentation M State)
    {window : M.atlas.Window}
    (nested : M.atlas.nested window presentation.window)
    (state : State) :
    (presentation.restrict nested state).object =
      M.atlas.restrictLocal nested (presentation.realize state).object :=
  rfl

end RepresentedStatePresentation

/-- Generator/form capability on states that are all presented as valid states
of the registered local equation.  The exact decomposition, sector estimate,
and generator representation remain primitive laws; this record does not
assert quasi-regularity, coercivity, a Beurling-Deny-LeJan decomposition, or
equation-specific analytic admissibility. -/
structure GeneratorForm (M : LocalModel.{u}) (State : Type v)
    [AddCommGroup State] [Module Real State] where
  statePresentation : RepresentedStatePresentation M State
  domain : Submodule Real State
  generator : State →ₗ[Real] State
  pairing : BilinearForm State
  form : BilinearForm State
  symmetricPart : BilinearForm State
  skewPart : BilinearForm State
  boundaryPart : BilinearForm State
  topology : FormTopology State
  closure : FormClosureLaw State domain form topology
  generator_representation : forall x, x ∈ domain -> forall y, y ∈ domain ->
    form x y = pairing (generator x) y
  decomposition : forall x y,
    form x y = symmetricPart x y + skewPart x y + boundaryPart x y
  symmetric : forall x y, symmetricPart x y = symmetricPart y x
  skew : forall x y, skewPart x y = -skewPart y x
  symmetric_nonnegative : forall x, x ∈ domain -> 0 <= symmetricPart x x
  sectorConstant : Real
  sectorConstant_nonnegative : 0 <= sectorConstant
  sector : forall x, x ∈ domain -> forall y, y ∈ domain ->
    abs (skewPart x y) <=
      sectorConstant * Real.sqrt (symmetricPart x x) *
        Real.sqrt (symmetricPart y y)

namespace GeneratorForm

/-- The represented equation state attached to a generator state. -/
def equationState {M : LocalModel.{u}} {State : Type v}
    [AddCommGroup State] [Module Real State]
    (form : GeneratorForm M State) (state : State) :
    EquationState M.equation form.statePresentation.window :=
  form.statePresentation.realize state

/-- Restrict the equation state attached to a generator state. -/
def restrictEquationState {M : LocalModel.{u}} {State : Type v}
    [AddCommGroup State] [Module Real State]
    (form : GeneratorForm M State) {window : M.atlas.Window}
    (nested : M.atlas.nested window form.statePresentation.window)
    (state : State) : EquationState M.equation window :=
  form.statePresentation.restrict nested state

@[simp]
theorem restrictEquationState_object {M : LocalModel.{u}} {State : Type v}
    [AddCommGroup State] [Module Real State]
    (form : GeneratorForm M State) {window : M.atlas.Window}
    (nested : M.atlas.nested window form.statePresentation.window)
    (state : State) :
    (form.restrictEquationState nested state).object =
      M.atlas.restrictLocal nested (form.equationState state).object :=
  rfl

/-- Core node that installs row 2 in the complete row-1 predecessor ledger. -/
def registrationNode {Previous : Sort uPrevious}
    {M : LocalModel.{u}} {State : Type v}
    [AddCommGroup State] [Module Real State]
    (capability : GeneratorForm M State) :
    Core.Residual.StageNode Previous (fun _ => GeneratorForm M State) :=
  Core.Residual.StageNode.create fun _ => capability

/-- Register row 2 through the generic accumulated-ledger executor. -/
def register {Previous : Sort uPrevious}
    {M : LocalModel.{u}} {State : Type v}
    [AddCommGroup State] [Module Real State]
    (capability : GeneratorForm M State) (previous : Previous) :=
  (registrationNode capability).run previous

@[simp]
theorem register_previous {Previous : Sort uPrevious}
    {M : LocalModel.{u}} {State : Type v}
    [AddCommGroup State] [Module Real State]
    (capability : GeneratorForm M State) (previous : Previous) :
    (register capability previous).previous = previous :=
  rfl

end GeneratorForm

end Hypostructure.PDE
