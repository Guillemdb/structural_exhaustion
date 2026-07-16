import StructuralExhaustion.Examples.LongPrefixFourthBlockClauseAlignment
import StructuralExhaustion.Graph.LongPrefixCompatibleResponseFrontier

namespace StructuralExhaustion.Examples.LongPrefixCompatibleResponseFrontier

open StructuralExhaustion

universe u

variable {V : Type u} {object : Graph.FiniteObject V}
variable {input : Graph.LongPrefixObservedLabel.Input object}
variable (firstThirtySix : 36 ≤ input.support.length)

noncomputable def source :
    Graph.LongPrefixCompatibleResponseFrontier.Source (input := input) where
  fourthSource := LongPrefixFourthBlockClauseAlignment.source firstThirtySix
  fourthResult := Graph.LongPrefixFourthBlockClauseAlignment.run
    (LongPrefixFourthBlockClauseAlignment.source firstThirtySix)
  fourthResultExact := rfl

noncomputable def result := Graph.LongPrefixCompatibleResponseFrontier.run
  (source firstThirtySix)

example : (result firstThirtySix).predecessor =
    (source firstThirtySix).fourthResult :=
  Graph.LongPrefixCompatibleResponseFrontier.run_predecessor _

example
    (predecessor : Graph.LongPrefixFourthBlockClauseAlignment.Result
      (source firstThirtySix).fourthSource) :
    (Graph.LongPrefixCompatibleResponseFrontier.pending
      (source firstThirtySix) predecessor).retained = predecessor ∧
    (Graph.LongPrefixCompatibleResponseFrontier.pending
      (source firstThirtySix) predecessor).needs =
        Graph.LongPrefixCompatibleResponseFrontier.required predecessor :=
  ⟨rfl, rfl⟩

example :
    (∃ mismatch obligation,
      result firstThirtySix = .inheritedFirstMismatch mismatch obligation) ∨
    (∃ first second obligation,
      result firstThirtySix = .inheritedSecondMismatch first second obligation) ∨
    (∃ first second third obligation,
      result firstThirtySix = .inheritedThirdMismatch first second third obligation) ∨
    (∃ first second third fourth obligation,
      result firstThirtySix = .fourthMismatch first second third fourth obligation) ∨
    (∃ first second third fourth obligation,
      result firstThirtySix =
        .firstThirtySixAligned first second third fourth obligation) :=
  Graph.LongPrefixCompatibleResponseFrontier.run_exhaustive _

example : Graph.LongPrefixCompatibleResponseFrontier.requiredInputs
    (source firstThirtySix) ≤ 3 :=
  Graph.LongPrefixCompatibleResponseFrontier.requiredInputs_le_three _

example : Graph.LongPrefixCompatibleResponseFrontier.visibleChecks ≤ 1 :=
  Graph.LongPrefixCompatibleResponseFrontier.visibleChecks_constant

end StructuralExhaustion.Examples.LongPrefixCompatibleResponseFrontier
