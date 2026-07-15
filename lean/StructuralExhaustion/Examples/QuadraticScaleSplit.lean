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

end StructuralExhaustion.Examples.QuadraticScaleSplit
