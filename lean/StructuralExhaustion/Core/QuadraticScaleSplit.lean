import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

namespace StructuralExhaustion.Core.QuadraticScaleSplit

/-!
# Constant-work quadratic scale split

Many structural-exhaustion proofs branch on whether a nonnegative load is
larger than a fixed square-root scale.  Squaring the comparison gives an
exact natural-number decision and avoids real arithmetic or numerical
approximation.  This module owns that reusable branch contract.
-/

structure Input where
  load : Nat
  coefficient : Nat
  order : Nat
  deriving Repr, DecidableEq

inductive Decision (input : Input) : Type
  | large (strict : input.coefficient * input.order < input.load ^ 2)
  | bounded (bound : input.load ^ 2 ≤ input.coefficient * input.order)

def decide (input : Input) : Decision input := by
  by_cases large : input.coefficient * input.order < input.load ^ 2
  · exact .large large
  · exact .bounded (by omega)

theorem exhaustive (input : Input) :
    input.coefficient * input.order < input.load ^ 2 ∨
      input.load ^ 2 ≤ input.coefficient * input.order := by
  cases decide input with
  | large strict => exact Or.inl strict
  | bounded bound => exact Or.inr bound

def checks (_input : Input) : Nat := 1

theorem checks_eq_one (input : Input) : checks input = 1 := rfl

structure VerifiedStage (input : Input) : Type where
  decision : Decision input
  total : input.coefficient * input.order < input.load ^ 2 ∨
    input.load ^ 2 ≤ input.coefficient * input.order
  work : checks input = 1

def verifiedStage (input : Input) : VerifiedStage input where
  decision := decide input
  total := exhaustive input
  work := checks_eq_one input

/-! ## Reusable bounded-branch asymptotics -/

/-- Real square-root envelope attached to the exact bounded branch. -/
noncomputable def boundedRealEnvelope (coefficient order : Nat) : ℝ :=
  Real.sqrt ((coefficient * order : Nat) : ℝ)

/-- A squared natural bound gives the corresponding real square-root bound
without any numerical approximation. -/
theorem load_cast_le_boundedRealEnvelope (input : Input)
    (bound : input.load ^ 2 ≤ input.coefficient * input.order) :
    (input.load : ℝ) ≤ boundedRealEnvelope input.coefficient input.order := by
  have squared : ((input.load : ℝ) ^ 2) ≤
      ((input.coefficient * input.order : Nat) : ℝ) := by
    exact_mod_cast bound
  calc
    (input.load : ℝ) = Real.sqrt ((input.load : ℝ) ^ 2) := by
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg]
      positivity
    _ ≤ Real.sqrt ((input.coefficient * input.order : Nat) : ℝ) :=
      Real.sqrt_le_sqrt squared
    _ = boundedRealEnvelope input.coefficient input.order := rfl

/-- For every fixed coefficient, the bounded-branch square-root envelope is
`o(n)`, expressed as its normalized ratio tending to zero. -/
theorem boundedRealEnvelope_div_order_tendsto_zero (coefficient : Nat) :
    Filter.Tendsto
      (fun order : Nat => boundedRealEnvelope coefficient order / (order : ℝ))
      Filter.atTop (nhds 0) := by
  have sqrtOrder : Filter.Tendsto
      (fun order : Nat => Real.sqrt (order : ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have quotient : Filter.Tendsto
      (fun order : Nat =>
        Real.sqrt (coefficient : ℝ) / Real.sqrt (order : ℝ))
      Filter.atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop sqrtOrder
  apply quotient.congr'
  filter_upwards [Filter.eventually_ge_atTop 1] with order horder
  have orderPositive : (0 : ℝ) < order := by exact_mod_cast horder
  unfold boundedRealEnvelope
  rw [show ((coefficient * order : Nat) : ℝ) =
      (coefficient : ℝ) * (order : ℝ) by norm_num]
  rw [Real.sqrt_mul (by positivity)]
  field_simp [Real.sqrt_ne_zero'.mpr orderPositive]
  rw [Real.sq_sqrt orderPositive.le]

/-- Uniform family form of the bounded-branch estimate. The coefficient is
fixed while the order tends to infinity; consequently the normalized load
tends to zero. -/
theorem boundedLoad_div_order_tendsto_zero
    {ι : Type*} {l : Filter ι} (coefficient : Nat)
    (load order : ι → Nat)
    (orderTop : Filter.Tendsto order l Filter.atTop)
    (bounded : ∀ᶠ i in l, load i ^ 2 ≤ coefficient * order i) :
    Filter.Tendsto (fun i => (load i : ℝ) / (order i : ℝ))
      l (nhds 0) := by
  have envelopeZero :=
    (boundedRealEnvelope_div_order_tendsto_zero coefficient).comp orderTop
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun _ => by positivity
  · filter_upwards [bounded, orderTop.eventually (Filter.eventually_ge_atTop 1)]
      with i hi horder
    have orderPositive : (0 : ℝ) < order i := by exact_mod_cast horder
    exact div_le_div_of_nonneg_right
      (load_cast_le_boundedRealEnvelope
        { load := load i, coefficient := coefficient, order := order i } hi)
      orderPositive.le
  · exact envelopeZero

end StructuralExhaustion.Core.QuadraticScaleSplit
