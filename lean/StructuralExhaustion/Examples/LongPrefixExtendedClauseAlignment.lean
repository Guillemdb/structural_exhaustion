import StructuralExhaustion.Graph.LongPrefixExtendedClauseAlignment

namespace StructuralExhaustion.Examples.LongPrefixExtendedClauseAlignment

open StructuralExhaustion

universe u

variable {V : Type u} {object : Graph.FiniteObject V}
variable {input : Graph.LongPrefixObservedLabel.Input object}
variable (firstEighteen : 18 ≤ input.support.length)

noncomputable def localSource :
    Graph.LongPrefixLocalClauseAlignment.Source (input := input) where
  degreeSource := ⟨Graph.LongPrefixObservedLabel.run input⟩
  degreeResult := Graph.LongPrefixDegreeRefinement.run
    ⟨Graph.LongPrefixObservedLabel.run input⟩
  degreeResultExact := rfl

noncomputable def source :
    Graph.LongPrefixExtendedClauseAlignment.Source (input := input) where
  localSource := localSource
  localResult := Graph.LongPrefixLocalClauseAlignment.run localSource
  localResultExact := rfl
  firstEighteen := firstEighteen

noncomputable def result :=
  Graph.LongPrefixExtendedClauseAlignment.run (source firstEighteen)

example :
    (∃ mismatch, result firstEighteen = .inheritedMismatch mismatch) ∨
    (∃ first second, result firstEighteen = .secondMismatch first second) ∨
    (∃ first second, result firstEighteen = .firstEighteenAligned first second) :=
  Graph.LongPrefixExtendedClauseAlignment.run_exhaustive _

example
    (mismatch : Graph.LongPrefixExtendedClauseAlignment.SecondMismatch
      (source firstEighteen)) :
    ¬((Graph.LongPrefixExtendedClauseAlignment.profile
        (source firstEighteen)).left mismatch.hit.value ↔
      (Graph.LongPrefixExtendedClauseAlignment.profile
        (source firstEighteen)).right mismatch.hit.value) :=
  mismatch.sound

example
    (aligned : Graph.LongPrefixExtendedClauseAlignment.SecondAligned
      (source firstEighteen)) :
    ∀ coordinate,
      (Graph.LongPrefixExtendedClauseAlignment.profile
        (source firstEighteen)).left coordinate ↔
      (Graph.LongPrefixExtendedClauseAlignment.profile
        (source firstEighteen)).right coordinate :=
  aligned.exact

example : Graph.LongPrefixExtendedClauseAlignment.visibleChecks ≤
    18 * (object.input.vertices.card + 1) :=
  Graph.LongPrefixExtendedClauseAlignment.visibleChecks_polynomial

end StructuralExhaustion.Examples.LongPrefixExtendedClauseAlignment
