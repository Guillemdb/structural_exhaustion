import StructuralExhaustion.Graph.LongPrefixThirdBlockClauseAlignment

namespace StructuralExhaustion.Examples.LongPrefixThirdBlockClauseAlignment

open StructuralExhaustion

universe u

variable {V : Type u} {object : Graph.FiniteObject V}
variable {input : Graph.LongPrefixObservedLabel.Input object}
variable (firstTwentySeven : 27 ≤ input.support.length)

noncomputable def localSource :
    Graph.LongPrefixLocalClauseAlignment.Source (input := input) where
  degreeSource := ⟨Graph.LongPrefixObservedLabel.run input⟩
  degreeResult := Graph.LongPrefixDegreeRefinement.run
    ⟨Graph.LongPrefixObservedLabel.run input⟩
  degreeResultExact := rfl

noncomputable def extendedSource :
    Graph.LongPrefixExtendedClauseAlignment.Source (input := input) where
  localSource := localSource
  localResult := Graph.LongPrefixLocalClauseAlignment.run localSource
  localResultExact := rfl
  firstEighteen := by omega

noncomputable def source :
    Graph.LongPrefixThirdBlockClauseAlignment.Source (input := input) where
  extendedSource := extendedSource firstTwentySeven
  extendedResult := Graph.LongPrefixExtendedClauseAlignment.run
    (extendedSource firstTwentySeven)
  extendedResultExact := rfl
  firstTwentySeven := firstTwentySeven

noncomputable def result :=
  Graph.LongPrefixThirdBlockClauseAlignment.run (source firstTwentySeven)

example :
    (∃ mismatch, result firstTwentySeven = .inheritedFirstMismatch mismatch) ∨
    (∃ first second,
      result firstTwentySeven = .inheritedSecondMismatch first second) ∨
    (∃ first second third,
      result firstTwentySeven = .thirdMismatch first second third) ∨
    (∃ first second third,
      result firstTwentySeven = .firstTwentySevenAligned first second third) :=
  Graph.LongPrefixThirdBlockClauseAlignment.run_exhaustive _

example
    (mismatch : Graph.LongPrefixThirdBlockClauseAlignment.ThirdMismatch
      (source firstTwentySeven)) :
    ¬((Graph.LongPrefixThirdBlockClauseAlignment.profile
        (source firstTwentySeven)).left mismatch.hit.value ↔
      (Graph.LongPrefixThirdBlockClauseAlignment.profile
        (source firstTwentySeven)).right mismatch.hit.value) :=
  mismatch.sound

example
    (aligned : Graph.LongPrefixThirdBlockClauseAlignment.ThirdAligned
      (source firstTwentySeven)) :
    ∀ coordinate,
      (Graph.LongPrefixThirdBlockClauseAlignment.profile
        (source firstTwentySeven)).left coordinate ↔
      (Graph.LongPrefixThirdBlockClauseAlignment.profile
        (source firstTwentySeven)).right coordinate :=
  aligned.exact

example : Graph.LongPrefixThirdBlockClauseAlignment.visibleChecks ≤
    18 * (object.input.vertices.card + 1) :=
  Graph.LongPrefixThirdBlockClauseAlignment.visibleChecks_polynomial

end StructuralExhaustion.Examples.LongPrefixThirdBlockClauseAlignment
