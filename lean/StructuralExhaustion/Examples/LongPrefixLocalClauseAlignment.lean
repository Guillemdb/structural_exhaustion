import StructuralExhaustion.Graph.LongPrefixLocalClauseAlignment
import StructuralExhaustion.Examples.OrderedBFSTree

namespace StructuralExhaustion.Examples.LongPrefixLocalClauseAlignment

open StructuralExhaustion

universe u

variable {V : Type u} {object : Graph.FiniteObject V}
variable {input : Graph.LongPrefixObservedLabel.Input object}

noncomputable def source :
    Graph.LongPrefixLocalClauseAlignment.Source (input := input) where
  degreeSource := ⟨Graph.LongPrefixObservedLabel.run input⟩
  degreeResult := Graph.LongPrefixDegreeRefinement.run ⟨
    Graph.LongPrefixObservedLabel.run input⟩
  degreeResultExact := rfl

noncomputable def result :=
  Graph.LongPrefixLocalClauseAlignment.run (source (input := input))

example :
    (∃ residual, result (input := input) = .firstMismatch residual) ∨
      (∃ residual, result (input := input) = .aligned residual) :=
  Graph.LongPrefixLocalClauseAlignment.run_exhaustive _

example
    (mismatch : Graph.LongPrefixLocalClauseAlignment.FirstMismatch
      (source (input := input))) :
    ¬((Graph.LongPrefixLocalClauseAlignment.profile
        (source (input := input))).left mismatch.hit.value ↔
      (Graph.LongPrefixLocalClauseAlignment.profile
        (source (input := input))).right mismatch.hit.value) :=
  mismatch.sound

example
    (aligned : Graph.LongPrefixLocalClauseAlignment.Aligned
      (source (input := input))) :
    ∀ coordinate,
      (Graph.LongPrefixLocalClauseAlignment.profile
        (source (input := input))).left coordinate ↔
      (Graph.LongPrefixLocalClauseAlignment.profile
        (source (input := input))).right coordinate :=
  aligned.exact

example : Graph.LongPrefixLocalClauseAlignment.visibleChecks ≤
    18 * (object.input.vertices.card + 1) :=
  Graph.LongPrefixLocalClauseAlignment.visibleChecks_polynomial

/-! Concrete branch executions on the textbook graph `K₅`. -/

def alignedInput : Graph.LongPrefixObservedLabel.Input
    OrderedBFSTreeK5.object where
  support := [0, 0, 0, 0, 0, 0, 0, 0, 0]
  marked := ∅
  firstNine := by decide

def mismatchInput : Graph.LongPrefixObservedLabel.Input
    OrderedBFSTreeK5.object where
  support := [0, 1, 2, 3, 4, 0, 1, 2, 3]
  marked := ∅
  firstNine := by decide

example : match result (input := alignedInput) with
  | .aligned .. => True
  | _ => False := by
  change True
  trivial

example : match result (input := mismatchInput) with
  | .firstMismatch .. => True
  | _ => False := by
  change True
  trivial

end StructuralExhaustion.Examples.LongPrefixLocalClauseAlignment
