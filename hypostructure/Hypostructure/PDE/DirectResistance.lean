import Mathlib.Data.ENNReal.Real
import Hypostructure.PDE.Quotient

/-!
# Direct effective-resistance capability

This module records the analytic content of the direct routing theorems for
one exact represented defect and one exact registered geometry. The framework
derives the routable and harmonic components from the registered projection;
applications do not supply either component as a row output.

The contract is intentionally theorem-shaped. A finite-dimensional profile
can prove it directly. A continuum profile must formalize or explicitly import
the corresponding spectral, weak-solution, energy, and drift theorems.
-/

namespace Hypostructure.PDE

universe uState uPotential

/-- Source-shaped direct-resistance laws for one exact defect current.

`harmonicProjection` is constrained by the exact `DefectGeometry` kernel and
orthogonality laws. `routableResistance` is the resistance of the derived
orthogonal component, not of a nonzero harmonic component. -/
structure DirectResistanceContract
    (State : Type uState)
    [NormedAddCommGroup State] [InnerProductSpace Real State]
    [CompleteSpace State]
    (geometry : DefectGeometry State) (defect : State)
    (Potential : Type uPotential) where
  harmonicProjection : State →L[Real] State
  projection_idempotent :
    harmonicProjection.comp harmonicProjection = harmonicProjection
  projection_symmetric : forall left right,
    inner Real (harmonicProjection left) right =
      inner Real left (harmonicProjection right)
  harmonic_is_harmonic :
    geometry.IsHarmonic (harmonicProjection defect)
  fixes_harmonic : forall state,
    geometry.IsHarmonic state -> harmonicProjection state = state
  routableResistance : ENNReal
  finiteDecidable : Decidable (routableResistance ≠ ⊤)
  action : Potential -> State
  energy : Potential -> Real
  energy_nonnegative : forall potential, 0 <= energy potential
  finite_of_compensator :
    (exists potential, action potential = defect - harmonicProjection defect) ->
      routableResistance ≠ ⊤
  compensator : routableResistance ≠ ⊤ -> Potential
  compensates : forall finite,
    action (compensator finite) = defect - harmonicProjection defect
  compensation_energy : forall finite,
    energy (compensator finite) = routableResistance.toReal
  minimal_energy : forall finite potential,
    action potential = defect - harmonicProjection defect ->
      energy (compensator finite) <= energy potential
  nonzero_harmonic_not_routable :
    harmonicProjection defect ≠ 0 ->
      ¬ (exists potential, action potential = harmonicProjection defect)
  symmetricEnergy : State -> Real
  symmetricEnergy_nonnegative : forall state, 0 <= symmetricEnergy state
  drift_bound : forall (_finite : routableResistance ≠ ⊤) state,
    abs (inner Real defect state) <=
      Real.sqrt routableResistance.toReal *
          Real.sqrt (symmetricEnergy state) +
        norm (harmonicProjection defect) * norm state

namespace DirectResistanceContract

variable {State : Type uState}
variable [NormedAddCommGroup State] [InnerProductSpace Real State]
variable [CompleteSpace State]
variable {geometry : DefectGeometry State} {defect : State}
variable {Potential : Type uPotential}

/-- Exact harmonic component derived by the framework. -/
def harmonic
    (contract : DirectResistanceContract State geometry defect Potential) : State :=
  contract.harmonicProjection defect

/-- Exact routable component derived by the framework. -/
def routable
    (contract : DirectResistanceContract State geometry defect Potential) : State :=
  defect - contract.harmonic

/-- Finite direct resistance of the derived routable component. -/
def Finite
    (contract : DirectResistanceContract State geometry defect Potential) : Prop :=
  contract.routableResistance ≠ ⊤

instance (contract : DirectResistanceContract State geometry defect Potential) :
    Decidable contract.Finite :=
  contract.finiteDecidable

/-- Finiteness is equivalent to existence of an exact compensator. The forward
direction is generated from the selected compensator; only the reverse
analytic implication is an author field. -/
theorem finite_iff_compensator
    (contract : DirectResistanceContract State geometry defect Potential) :
    contract.Finite <->
      exists potential, contract.action potential = contract.routable := by
  constructor
  · intro finite
    exact ⟨contract.compensator finite, contract.compensates finite⟩
  · exact contract.finite_of_compensator

/-- The registered projection yields the literal source decomposition. -/
@[simp] theorem routable_add_harmonic
    (contract : DirectResistanceContract State geometry defect Potential) :
    contract.routable + contract.harmonic = defect := by
  simp [routable, harmonic]

/-- The derived harmonic component belongs to the registered geometry kernel. -/
theorem harmonic_is_kernel
    (contract : DirectResistanceContract State geometry defect Potential) :
    geometry.IsHarmonic contract.harmonic :=
  contract.harmonic_is_harmonic

/-- The derived routable component is orthogonal to every registered harmonic
state. -/
theorem routable_inner_harmonic
    (contract : DirectResistanceContract State geometry defect Potential)
    (state : State) (isHarmonic : geometry.IsHarmonic state) :
    inner Real contract.routable state = 0 :=
  by
    rw [routable, harmonic, inner_sub_left,
      contract.projection_symmetric,
      contract.fixes_harmonic state isHarmonic, sub_self]

end DirectResistanceContract

end Hypostructure.PDE

#print axioms Hypostructure.PDE.DirectResistanceContract.routable_add_harmonic
#print axioms Hypostructure.PDE.DirectResistanceContract.harmonic_is_kernel
#print axioms Hypostructure.PDE.DirectResistanceContract.routable_inner_harmonic
#print axioms Hypostructure.PDE.DirectResistanceContract.finite_iff_compensator
