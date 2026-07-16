import StructuralExhaustion.Graph.LongPrefixThirdBlockClauseAlignment

namespace StructuralExhaustion.Graph.LongPrefixFourthBlockClauseAlignment

open StructuralExhaustion

universe u

/-! Fourth fixed block of literal long-prefix adjacency clauses. -/

variable {V : Type u} {object : FiniteObject V}
variable {input : LongPrefixObservedLabel.Input object}

structure Source where
  thirdSource : LongPrefixThirdBlockClauseAlignment.Source (input := input)
  thirdResult : LongPrefixThirdBlockClauseAlignment.Result thirdSource
  thirdResultExact : thirdResult =
    LongPrefixThirdBlockClauseAlignment.run thirdSource
  firstThirtySix : 36 ≤ input.support.length

abbrev Coordinate := Fin 9

def supportPosition (source : Source (input := input))
    (coordinate : Coordinate) : Fin input.support.length :=
  ⟨coordinate.1 + 27, by
    have bound := source.firstThirtySix
    omega⟩

def vertex (source : Source (input := input))
    (coordinate : Coordinate) : V :=
  input.support.get (supportPosition source coordinate)

noncomputable def profile (source : Source (input := input)) :
    Core.FinitePredicateAlignment.Profile where
  Coordinate := Coordinate
  coordinates := by infer_instance
  left := fun coordinate => object.graph.Adj
    source.thirdSource.extendedSource.localSource.degreeSource.firstVertex
    (vertex source coordinate)
  right := fun coordinate => object.graph.Adj
    source.thirdSource.extendedSource.localSource.degreeSource.secondVertex
    (vertex source coordinate)
  leftDecidable := fun coordinate => object.input.decideAdj
    source.thirdSource.extendedSource.localSource.degreeSource.firstVertex
    (vertex source coordinate)
  rightDecidable := fun coordinate => object.input.decideAdj
    source.thirdSource.extendedSource.localSource.degreeSource.secondVertex
    (vertex source coordinate)

structure FourthMismatch (source : Source (input := input)) where
  hit : Core.FiniteSearch.FirstHit (profile source).coordinates.orderedValues
    (profile source).Mismatch

namespace FourthMismatch

variable {source : Source (input := input)}

theorem sound (mismatch : FourthMismatch source) :
    ¬((profile source).left mismatch.hit.value ↔
      (profile source).right mismatch.hit.value) :=
  Core.FinitePredicateAlignment.Profile.mismatch_sound (profile source)
    mismatch.hit

theorem prefixExact (mismatch : FourthMismatch source) :
    ∀ coordinate, coordinate ∈ mismatch.hit.before →
      ((profile source).left coordinate ↔
        (profile source).right coordinate) :=
  Core.FinitePredicateAlignment.Profile.mismatch_prefix_exact (profile source)
    mismatch.hit

end FourthMismatch

structure FourthAligned (source : Source (input := input)) where
  exact : ∀ coordinate,
    (profile source).left coordinate ↔ (profile source).right coordinate

inductive Result (source : Source (input := input)) where
  | inheritedFirstMismatch
      (mismatch : LongPrefixLocalClauseAlignment.FirstMismatch
        source.thirdSource.extendedSource.localSource)
  | inheritedSecondMismatch
      (first : LongPrefixLocalClauseAlignment.Aligned
        source.thirdSource.extendedSource.localSource)
      (second : LongPrefixExtendedClauseAlignment.SecondMismatch
        source.thirdSource.extendedSource)
  | inheritedThirdMismatch
      (first : LongPrefixLocalClauseAlignment.Aligned
        source.thirdSource.extendedSource.localSource)
      (second : LongPrefixExtendedClauseAlignment.SecondAligned
        source.thirdSource.extendedSource)
      (third : LongPrefixThirdBlockClauseAlignment.ThirdMismatch source.thirdSource)
  | fourthMismatch
      (first : LongPrefixLocalClauseAlignment.Aligned
        source.thirdSource.extendedSource.localSource)
      (second : LongPrefixExtendedClauseAlignment.SecondAligned
        source.thirdSource.extendedSource)
      (third : LongPrefixThirdBlockClauseAlignment.ThirdAligned source.thirdSource)
      (fourth : FourthMismatch source)
  | firstThirtySixAligned
      (first : LongPrefixLocalClauseAlignment.Aligned
        source.thirdSource.extendedSource.localSource)
      (second : LongPrefixExtendedClauseAlignment.SecondAligned
        source.thirdSource.extendedSource)
      (third : LongPrefixThirdBlockClauseAlignment.ThirdAligned source.thirdSource)
      (fourth : FourthAligned source)

noncomputable def run (source : Source (input := input)) : Result source :=
  match source.thirdResult with
  | .inheritedFirstMismatch mismatch => .inheritedFirstMismatch mismatch
  | .inheritedSecondMismatch first second =>
      .inheritedSecondMismatch first second
  | .thirdMismatch first second third =>
      .inheritedThirdMismatch first second third
  | .firstTwentySevenAligned first second third =>
      match (profile source).decide with
      | .mismatch hit => .fourthMismatch first second third ⟨hit⟩
      | .aligned exact => .firstThirtySixAligned first second third ⟨exact⟩

theorem run_exhaustive (source : Source (input := input)) :
    (∃ mismatch, run source = .inheritedFirstMismatch mismatch) ∨
    (∃ first second, run source = .inheritedSecondMismatch first second) ∨
    (∃ first second third,
      run source = .inheritedThirdMismatch first second third) ∨
    (∃ first second third fourth,
      run source = .fourthMismatch first second third fourth) ∨
    (∃ first second third fourth,
      run source = .firstThirtySixAligned first second third fourth) := by
  cases equation : run source with
  | inheritedFirstMismatch mismatch => exact Or.inl ⟨mismatch, rfl⟩
  | inheritedSecondMismatch first second =>
      exact Or.inr (Or.inl ⟨first, second, rfl⟩)
  | inheritedThirdMismatch first second third =>
      exact Or.inr (Or.inr (Or.inl ⟨first, second, third, rfl⟩))
  | fourthMismatch first second third fourth =>
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨first, second, third, fourth, rfl⟩)))
  | firstThirtySixAligned first second third fourth =>
      exact Or.inr (Or.inr (Or.inr (Or.inr
        ⟨first, second, third, fourth, rfl⟩)))

theorem source_third_exact (source : Source (input := input)) :
    source.thirdResult = LongPrefixThirdBlockClauseAlignment.run source.thirdSource :=
  source.thirdResultExact

def visibleChecks : Nat := 18

theorem visibleChecks_polynomial :
    visibleChecks ≤ 18 * (object.input.vertices.card + 1) := by
  unfold visibleChecks
  omega

end StructuralExhaustion.Graph.LongPrefixFourthBlockClauseAlignment
