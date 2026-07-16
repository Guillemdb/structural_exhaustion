import StructuralExhaustion.Graph.LongPrefixLocalClauseAlignment

namespace StructuralExhaustion.Graph.LongPrefixExtendedClauseAlignment

open StructuralExhaustion

universe u

/-!
# Second-block local adjacency-clause alignment

This profile consumes the exact first-nine result.  An existing mismatch is
preserved.  Only an aligned result triggers a scan of the next nine literal
support positions, giving a first mismatch there or exact alignment over the
two declared blocks.  The schedule is fixed by the supplied support and never
expanded into an ambient response or context universe.
-/

variable {V : Type u} {object : FiniteObject V}
variable {input : LongPrefixObservedLabel.Input object}

structure Source where
  localSource : LongPrefixLocalClauseAlignment.Source (input := input)
  localResult : LongPrefixLocalClauseAlignment.Result localSource
  localResultExact : localResult = LongPrefixLocalClauseAlignment.run localSource
  firstEighteen : 18 ≤ input.support.length

/-- Coordinates within the second fixed block; literal support indices are
obtained by adding nine. -/
abbrev Coordinate := Fin 9

def supportPosition (source : Source (input := input))
    (coordinate : Coordinate) : Fin input.support.length :=
  ⟨coordinate.1 + 9, by
    have bound := source.firstEighteen
    omega⟩

def vertex (source : Source (input := input))
    (coordinate : Coordinate) : V :=
  input.support.get (supportPosition source coordinate)

noncomputable def profile (source : Source (input := input)) :
    Core.FinitePredicateAlignment.Profile where
  Coordinate := Coordinate
  coordinates := by infer_instance
  left := fun coordinate => object.graph.Adj
    source.localSource.degreeSource.firstVertex (vertex source coordinate)
  right := fun coordinate => object.graph.Adj
    source.localSource.degreeSource.secondVertex (vertex source coordinate)
  leftDecidable := fun coordinate => object.input.decideAdj
    source.localSource.degreeSource.firstVertex (vertex source coordinate)
  rightDecidable := fun coordinate => object.input.decideAdj
    source.localSource.degreeSource.secondVertex (vertex source coordinate)

structure SecondMismatch (source : Source (input := input)) where
  hit : Core.FiniteSearch.FirstHit (profile source).coordinates.orderedValues
    (profile source).Mismatch

namespace SecondMismatch

variable {source : Source (input := input)}

theorem sound (mismatch : SecondMismatch source) :
    ¬((profile source).left mismatch.hit.value ↔
      (profile source).right mismatch.hit.value) :=
  Core.FinitePredicateAlignment.Profile.mismatch_sound (profile source)
    mismatch.hit

theorem prefixExact (mismatch : SecondMismatch source) :
    ∀ coordinate, coordinate ∈ mismatch.hit.before →
      ((profile source).left coordinate ↔
        (profile source).right coordinate) :=
  Core.FinitePredicateAlignment.Profile.mismatch_prefix_exact (profile source)
    mismatch.hit

end SecondMismatch

structure SecondAligned (source : Source (input := input)) where
  exact : ∀ coordinate,
    (profile source).left coordinate ↔ (profile source).right coordinate

inductive Result (source : Source (input := input)) where
  | inheritedMismatch
      (mismatch : LongPrefixLocalClauseAlignment.FirstMismatch source.localSource)
  | secondMismatch
      (first : LongPrefixLocalClauseAlignment.Aligned source.localSource)
      (second : SecondMismatch source)
  | firstEighteenAligned
      (first : LongPrefixLocalClauseAlignment.Aligned source.localSource)
      (second : SecondAligned source)

/-- Preserve an existing mismatch; otherwise scan precisely positions 9--17. -/
noncomputable def run (source : Source (input := input)) : Result source :=
  match source.localResult with
  | .firstMismatch mismatch => .inheritedMismatch mismatch
  | .aligned first =>
      match (profile source).decide with
      | .mismatch hit => .secondMismatch first ⟨hit⟩
      | .aligned exact => .firstEighteenAligned first ⟨exact⟩

theorem run_exhaustive (source : Source (input := input)) :
    (∃ mismatch, run source = .inheritedMismatch mismatch) ∨
    (∃ first second, run source = .secondMismatch first second) ∨
    (∃ first second, run source = .firstEighteenAligned first second) := by
  cases equation : run source with
  | inheritedMismatch mismatch => exact Or.inl ⟨mismatch, rfl⟩
  | secondMismatch first second => exact Or.inr (Or.inl ⟨first, second, rfl⟩)
  | firstEighteenAligned first second =>
      exact Or.inr (Or.inr ⟨first, second, rfl⟩)

theorem source_local_exact (source : Source (input := input)) :
    source.localResult = LongPrefixLocalClauseAlignment.run source.localSource :=
  source.localResultExact

/-- The inherited-mismatch branch costs zero; the uniform upper ledger charges
two adjacency evaluations at each of nine second-block coordinates. -/
def visibleChecks : Nat := 18

theorem visibleChecks_polynomial :
    visibleChecks ≤ 18 * (object.input.vertices.card + 1) := by
  unfold visibleChecks
  omega

end StructuralExhaustion.Graph.LongPrefixExtendedClauseAlignment
