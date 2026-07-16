import StructuralExhaustion.Core.FinitePredicateAlignment
import StructuralExhaustion.Graph.LongPrefixDegreeRefinement

namespace StructuralExhaustion.Graph.LongPrefixLocalClauseAlignment

open StructuralExhaustion

universe u

/-!
# Local adjacency-clause alignment after the long-prefix degree fork

The only response coordinates inspected here are the nine literal prefix
occurrences already exposed by `LongPrefixObservedLabel`.  For each such
coordinate, the runner compares adjacency from the two retained collision
vertices.  It returns the first differing local clause or exact agreement on
this nine-coordinate schedule.

Agreement on this schedule is not complete D4--D7 response equivalence and
does not authorize CT8 removal.  No ambient response, context, state, path,
graph, or vertex universe is enumerated.
-/

variable {V : Type u} {object : FiniteObject V}
variable {input : LongPrefixObservedLabel.Input object}

/-- Exact node-179 graph result and its execution equality. -/
structure Source where
  degreeSource : LongPrefixDegreeRefinement.Source (input := input)
  degreeResult : LongPrefixDegreeRefinement.Result degreeSource
  degreeResultExact : degreeResult = LongPrefixDegreeRefinement.run degreeSource

/-- The declared response coordinates are exactly the first nine actual
prefix occurrences; this is not an ambient context enumeration. -/
abbrev Coordinate := LongPrefixObservedLabel.Occurrence

noncomputable def profile (source : Source (input := input)) :
    Core.FinitePredicateAlignment.Profile where
  Coordinate := Coordinate
  coordinates := LongPrefixObservedLabel.occurrences
  left := fun coordinate => object.graph.Adj source.degreeSource.firstVertex
    (LongPrefixObservedLabel.vertex input coordinate)
  right := fun coordinate => object.graph.Adj source.degreeSource.secondVertex
    (LongPrefixObservedLabel.vertex input coordinate)
  leftDecidable := fun coordinate => object.input.decideAdj
    source.degreeSource.firstVertex
    (LongPrefixObservedLabel.vertex input coordinate)
  rightDecidable := fun coordinate => object.input.decideAdj
    source.degreeSource.secondVertex
    (LongPrefixObservedLabel.vertex input coordinate)

structure FirstMismatch (source : Source (input := input)) where
  hit : Core.FiniteSearch.FirstHit (profile source).coordinates.orderedValues
    (profile source).Mismatch

namespace FirstMismatch

variable {source : Source (input := input)}

theorem sound (mismatch : FirstMismatch source) :
    ¬((profile source).left mismatch.hit.value ↔
      (profile source).right mismatch.hit.value) :=
  Core.FinitePredicateAlignment.Profile.mismatch_sound (profile source)
    mismatch.hit

theorem prefixExact (mismatch : FirstMismatch source) :
    ∀ coordinate, coordinate ∈ mismatch.hit.before →
      ((profile source).left coordinate ↔
        (profile source).right coordinate) :=
  Core.FinitePredicateAlignment.Profile.mismatch_prefix_exact (profile source)
    mismatch.hit

end FirstMismatch

structure Aligned (source : Source (input := input)) where
  exact : ∀ coordinate,
    (profile source).left coordinate ↔ (profile source).right coordinate

inductive Result (source : Source (input := input)) where
  | firstMismatch (residual : FirstMismatch source)
  | aligned (residual : Aligned source)

/-- Execute the reusable first-disagreement scan on the fixed local schedule. -/
noncomputable def run (source : Source (input := input)) : Result source :=
  match (profile source).decide with
  | .mismatch hit => .firstMismatch ⟨hit⟩
  | .aligned exact => .aligned ⟨exact⟩

theorem run_exhaustive (source : Source (input := input)) :
    (∃ residual, run source = .firstMismatch residual) ∨
      (∃ residual, run source = .aligned residual) := by
  cases equation : run source with
  | firstMismatch residual => exact Or.inl ⟨residual, rfl⟩
  | aligned residual => exact Or.inr ⟨residual, rfl⟩

theorem source_degree_exact (source : Source (input := input)) :
    source.degreeResult = LongPrefixDegreeRefinement.run source.degreeSource :=
  source.degreeResultExact

/-- Nine coordinates, with one adjacency predicate evaluated at each of two
retained vertices. -/
def visibleChecks : Nat := 18

theorem visibleChecks_constant : visibleChecks = 18 := rfl

theorem visibleChecks_polynomial :
    visibleChecks ≤ 18 * (object.input.vertices.card + 1) := by
  unfold visibleChecks
  omega

end StructuralExhaustion.Graph.LongPrefixLocalClauseAlignment
