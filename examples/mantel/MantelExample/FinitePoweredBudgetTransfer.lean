import MantelExample.Concrete
import StructuralExhaustion.Core.FinitePoweredBudgetTransfer

namespace MantelExample.FinitePoweredBudgetTransfer

open StructuralExhaustion

/-!
# Powered-budget transfer on the actual Mantel `C₅`

The concrete cycle has five vertices and ten darts.  Its dart count is exactly
two orientation slots per vertex, while the square of its vertex count is
strictly below the next natural number.  These actual graph cardinalities
exercise the reusable symbolic transfer without evaluating a graph universe
or constructing a product schedule.
-/

/-- The Core profile instantiated with the concrete `C₅` vertex and dart
counts. -/
def profile : Core.FinitePoweredBudgetTransfer.Profile where
  forced := ConcreteC5.object.input.darts.card
  flat := 2
  stateCount := ConcreteC5.object.input.vertices.card
  upper := ConcreteC5.object.input.vertices.card ^ 2 + 1
  scale := 2
  forced_le_flat_mul_stateCount := by native_decide
  stateCount_pow_lt_upper := by native_decide
  flat_pos := by decide

/-- The concrete inputs are `10 ≤ 2·5` and `5² < 26`. -/
theorem inputs_exact :
    profile.forced = 10 ∧ profile.flat = 2 ∧
      profile.stateCount = 5 ∧ profile.upper = 26 ∧ profile.scale = 2 := by
  native_decide

/-- The shared theorem gives the exact strict powered fit `10² < 2²·26`. -/
theorem poweredFit :
    profile.forced ^ profile.scale <
      profile.flat ^ profile.scale * profile.upper :=
  profile.forced_pow_lt_flat_pow_mul_upper

/-- Symbolic transfer performs no semantic graph checks. -/
theorem checks_exact : profile.checks = 0 := profile.checks_eq_zero

/-- The transfer consumes the same concrete triangle-free object as the
external Mantel proof. -/
theorem source_triangleFree : ConcreteC5.object.graph.CliqueFree 3 :=
  ConcreteC5.triangleFree

/-- The same object satisfies the imported Mantel conclusion. -/
theorem source_mantel_bound : Target ConcreteC5.object :=
  ConcreteC5.mantel_bound

end MantelExample.FinitePoweredBudgetTransfer
