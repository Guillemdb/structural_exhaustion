import StructuralExhaustion.Core.QuadraticScaleSplit

namespace StructuralExhaustion.Examples.QuadraticScaleSplit

open Core.QuadraticScaleSplit

/-- The textbook comparison `7² > 3·16`, verified by the generic stage. -/
def largeInput : Input := ⟨7, 3, 16⟩

example : largeInput.coefficient * largeInput.order < largeInput.load ^ 2 := by
  decide

example : (verifiedStage largeInput).work = rfl := rfl

/-- The complementary textbook comparison `6² ≤ 3·16`. -/
def boundedInput : Input := ⟨6, 3, 16⟩

example : boundedInput.load ^ 2 ≤
    boundedInput.coefficient * boundedInput.order := by
  decide

example : (boundedInput.load : ℝ) ≤
    boundedRealEnvelope boundedInput.coefficient boundedInput.order :=
  load_cast_le_boundedRealEnvelope boundedInput (by decide)

example : Filter.Tendsto
    (fun n : Nat => boundedRealEnvelope 3 n / (n : ℝ))
    Filter.atTop (nhds 0) :=
  boundedRealEnvelope_div_order_tendsto_zero 3

example : Filter.Tendsto
    (fun n : Nat => (0 : ℝ) / n)
    Filter.atTop (nhds 0) := by
  have bounded : ∀ᶠ n : Nat in Filter.atTop, 0 ^ 2 ≤ 3 * n :=
    Filter.Eventually.of_forall fun n => by simp
  simpa using boundedLoad_div_order_tendsto_zero
    (l := Filter.atTop) 3 (fun _n : Nat => 0) (fun n : Nat => n)
      tendsto_id bounded

end StructuralExhaustion.Examples.QuadraticScaleSplit
