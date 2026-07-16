import StructuralExhaustion.Graph.LongPrefixExtendedClauseAlignment

namespace StructuralExhaustion.Graph.LongPrefixThirdBlockClauseAlignment

open StructuralExhaustion

universe u

/-!
# Third-block local adjacency-clause alignment

This is the exact next consumer of the first-eighteen classifier.  Existing
mismatches pass through without new work.  Only the fully aligned predecessor
scans literal support positions 18--26.  The output remains a bounded local
adjacency statement and carries no complete response or CT8 semantics.
-/

variable {V : Type u} {object : FiniteObject V}
variable {input : LongPrefixObservedLabel.Input object}

structure Source where
  extendedSource : LongPrefixExtendedClauseAlignment.Source (input := input)
  extendedResult : LongPrefixExtendedClauseAlignment.Result extendedSource
  extendedResultExact : extendedResult =
    LongPrefixExtendedClauseAlignment.run extendedSource
  firstTwentySeven : 27 ≤ input.support.length

abbrev Coordinate := Fin 9

def supportPosition (source : Source (input := input))
    (coordinate : Coordinate) : Fin input.support.length :=
  ⟨coordinate.1 + 18, by
    have bound := source.firstTwentySeven
    omega⟩

def vertex (source : Source (input := input))
    (coordinate : Coordinate) : V :=
  input.support.get (supportPosition source coordinate)

noncomputable def profile (source : Source (input := input)) :
    Core.FinitePredicateAlignment.Profile where
  Coordinate := Coordinate
  coordinates := by infer_instance
  left := fun coordinate => object.graph.Adj
    source.extendedSource.localSource.degreeSource.firstVertex
    (vertex source coordinate)
  right := fun coordinate => object.graph.Adj
    source.extendedSource.localSource.degreeSource.secondVertex
    (vertex source coordinate)
  leftDecidable := fun coordinate => object.input.decideAdj
    source.extendedSource.localSource.degreeSource.firstVertex
    (vertex source coordinate)
  rightDecidable := fun coordinate => object.input.decideAdj
    source.extendedSource.localSource.degreeSource.secondVertex
    (vertex source coordinate)

structure ThirdMismatch (source : Source (input := input)) where
  hit : Core.FiniteSearch.FirstHit (profile source).coordinates.orderedValues
    (profile source).Mismatch

namespace ThirdMismatch

variable {source : Source (input := input)}

theorem sound (mismatch : ThirdMismatch source) :
    ¬((profile source).left mismatch.hit.value ↔
      (profile source).right mismatch.hit.value) :=
  Core.FinitePredicateAlignment.Profile.mismatch_sound (profile source)
    mismatch.hit

theorem prefixExact (mismatch : ThirdMismatch source) :
    ∀ coordinate, coordinate ∈ mismatch.hit.before →
      ((profile source).left coordinate ↔
        (profile source).right coordinate) :=
  Core.FinitePredicateAlignment.Profile.mismatch_prefix_exact (profile source)
    mismatch.hit

end ThirdMismatch

structure ThirdAligned (source : Source (input := input)) where
  exact : ∀ coordinate,
    (profile source).left coordinate ↔ (profile source).right coordinate

inductive Result (source : Source (input := input)) where
  | inheritedFirstMismatch
      (mismatch : LongPrefixLocalClauseAlignment.FirstMismatch
        source.extendedSource.localSource)
  | inheritedSecondMismatch
      (first : LongPrefixLocalClauseAlignment.Aligned
        source.extendedSource.localSource)
      (second : LongPrefixExtendedClauseAlignment.SecondMismatch
        source.extendedSource)
  | thirdMismatch
      (first : LongPrefixLocalClauseAlignment.Aligned
        source.extendedSource.localSource)
      (second : LongPrefixExtendedClauseAlignment.SecondAligned
        source.extendedSource)
      (third : ThirdMismatch source)
  | firstTwentySevenAligned
      (first : LongPrefixLocalClauseAlignment.Aligned
        source.extendedSource.localSource)
      (second : LongPrefixExtendedClauseAlignment.SecondAligned
        source.extendedSource)
      (third : ThirdAligned source)

noncomputable def run (source : Source (input := input)) : Result source :=
  match source.extendedResult with
  | .inheritedMismatch mismatch => .inheritedFirstMismatch mismatch
  | .secondMismatch first second => .inheritedSecondMismatch first second
  | .firstEighteenAligned first second =>
      match (profile source).decide with
      | .mismatch hit => .thirdMismatch first second ⟨hit⟩
      | .aligned exact => .firstTwentySevenAligned first second ⟨exact⟩

theorem run_exhaustive (source : Source (input := input)) :
    (∃ mismatch, run source = .inheritedFirstMismatch mismatch) ∨
    (∃ first second, run source = .inheritedSecondMismatch first second) ∨
    (∃ first second third, run source = .thirdMismatch first second third) ∨
    (∃ first second third,
      run source = .firstTwentySevenAligned first second third) := by
  cases equation : run source with
  | inheritedFirstMismatch mismatch => exact Or.inl ⟨mismatch, rfl⟩
  | inheritedSecondMismatch first second =>
      exact Or.inr (Or.inl ⟨first, second, rfl⟩)
  | thirdMismatch first second third =>
      exact Or.inr (Or.inr (Or.inl ⟨first, second, third, rfl⟩))
  | firstTwentySevenAligned first second third =>
      exact Or.inr (Or.inr (Or.inr ⟨first, second, third, rfl⟩))

theorem source_extended_exact (source : Source (input := input)) :
    source.extendedResult =
      LongPrefixExtendedClauseAlignment.run source.extendedSource :=
  source.extendedResultExact

/-- At most two adjacency evaluations on each of nine new coordinates. -/
def visibleChecks : Nat := 18

theorem visibleChecks_polynomial :
    visibleChecks ≤ 18 * (object.input.vertices.card + 1) := by
  unfold visibleChecks
  omega

end StructuralExhaustion.Graph.LongPrefixThirdBlockClauseAlignment
