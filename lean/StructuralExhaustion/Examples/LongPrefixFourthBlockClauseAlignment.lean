import StructuralExhaustion.Graph.LongPrefixFourthBlockClauseAlignment

namespace StructuralExhaustion.Examples.LongPrefixFourthBlockClauseAlignment

open StructuralExhaustion

universe u

variable {V : Type u} {object : Graph.FiniteObject V}
variable {input : Graph.LongPrefixObservedLabel.Input object}
variable (firstThirtySix : 36 ≤ input.support.length)

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

noncomputable def thirdSource :
    Graph.LongPrefixThirdBlockClauseAlignment.Source (input := input) where
  extendedSource := extendedSource firstThirtySix
  extendedResult := Graph.LongPrefixExtendedClauseAlignment.run
    (extendedSource firstThirtySix)
  extendedResultExact := rfl
  firstTwentySeven := by omega

noncomputable def source :
    Graph.LongPrefixFourthBlockClauseAlignment.Source (input := input) where
  thirdSource := thirdSource firstThirtySix
  thirdResult := Graph.LongPrefixThirdBlockClauseAlignment.run
    (thirdSource firstThirtySix)
  thirdResultExact := rfl
  firstThirtySix := firstThirtySix

noncomputable def result :=
  Graph.LongPrefixFourthBlockClauseAlignment.run (source firstThirtySix)

example :
    (∃ mismatch, result firstThirtySix = .inheritedFirstMismatch mismatch) ∨
    (∃ first second, result firstThirtySix = .inheritedSecondMismatch first second) ∨
    (∃ first second third,
      result firstThirtySix = .inheritedThirdMismatch first second third) ∨
    (∃ first second third fourth,
      result firstThirtySix = .fourthMismatch first second third fourth) ∨
    (∃ first second third fourth,
      result firstThirtySix = .firstThirtySixAligned first second third fourth) :=
  Graph.LongPrefixFourthBlockClauseAlignment.run_exhaustive _

example
    (mismatch : Graph.LongPrefixFourthBlockClauseAlignment.FourthMismatch
      (source firstThirtySix)) :
    ¬((Graph.LongPrefixFourthBlockClauseAlignment.profile
        (source firstThirtySix)).left mismatch.hit.value ↔
      (Graph.LongPrefixFourthBlockClauseAlignment.profile
        (source firstThirtySix)).right mismatch.hit.value) :=
  mismatch.sound

example
    (aligned : Graph.LongPrefixFourthBlockClauseAlignment.FourthAligned
      (source firstThirtySix)) :
    ∀ coordinate,
      (Graph.LongPrefixFourthBlockClauseAlignment.profile
        (source firstThirtySix)).left coordinate ↔
      (Graph.LongPrefixFourthBlockClauseAlignment.profile
        (source firstThirtySix)).right coordinate :=
  aligned.exact

example : Graph.LongPrefixFourthBlockClauseAlignment.visibleChecks ≤
    18 * (object.input.vertices.card + 1) :=
  Graph.LongPrefixFourthBlockClauseAlignment.visibleChecks_polynomial

end StructuralExhaustion.Examples.LongPrefixFourthBlockClauseAlignment
