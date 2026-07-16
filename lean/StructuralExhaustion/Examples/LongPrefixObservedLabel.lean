import StructuralExhaustion.Routes.LongPrefixObservedLabel

namespace StructuralExhaustion.Examples.LongPrefixObservedLabel

open StructuralExhaustion

universe u

/-! Theorem-independent transfer of the observed-label classifier. -/

variable {V : Type u} (object : Graph.FiniteObject V)
variable (support : List V) (marked : Finset V) (firstNine : 9 ≤ support.length)

noncomputable def input : Graph.LongPrefixObservedLabel.Input object :=
  ⟨support, marked, firstNine⟩

noncomputable def result := Graph.LongPrefixObservedLabel.run
  (input object support marked firstNine)

example :
    (result object support marked firstNine).repetition.collision.first ≠
      (result object support marked firstNine).repetition.collision.second :=
  Graph.LongPrefixObservedLabel.run_distinct _

example :
    Graph.LongPrefixObservedLabel.label (input object support marked firstNine)
        (result object support marked firstNine).repetition.collision.first =
      Graph.LongPrefixObservedLabel.label (input object support marked firstNine)
        (result object support marked firstNine).repetition.collision.second :=
  Graph.LongPrefixObservedLabel.run_sameLabel _

example : Graph.LongPrefixObservedLabel.visibleChecks
      (input object support marked firstNine) ≤
    144 * (object.input.vertices.card + 1) :=
  Graph.LongPrefixObservedLabel.visibleChecks_le _

example := Graph.LongPrefixObservedLabel.run_decision_exact
  (input object support marked firstNine)

abbrev problem : Core.Problem where
  Ambient := Unit
  Baseline := fun _ => True
  rank := fun _ => 0
  BranchState := fun _ => Unit

def context : Core.BranchContext problem := ⟨(), trivial, ()⟩

noncomputable def routed := Routes.LongPrefixObservedLabel.route
  (ctx := context)
  ⟨result object support marked firstNine⟩

example : (routed object support marked firstNine).classification.terminal =
    .promoted := by
  rw [(routed object support marked firstNine).classificationExact]
  exact Routes.LongPrefixObservedLabel.semantic_terminal_promoted _ _

example : (routed object support marked firstNine).classification.trace =
    [.entry, .table, .direct, .missing, .promotion, .promotedTerminal] := by
  rw [(routed object support marked firstNine).classificationExact]
  exact Routes.LongPrefixObservedLabel.semantic_run_trace _ _

example := Routes.LongPrefixObservedLabel.semantic_run_verified context
  (result object support marked firstNine)

example := Routes.LongPrefixObservedLabel.semantic_run_trace_valid context
  (result object support marked firstNine)

example := Routes.LongPrefixObservedLabel.semantic_run_total context
  (result object support marked firstNine)

example : Routes.LongPrefixObservedLabel.semanticChecks
    (result object support marked firstNine) = 9 := by simp

end StructuralExhaustion.Examples.LongPrefixObservedLabel
