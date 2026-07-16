import StructuralExhaustion.Graph.LongPrefixObservedLabel

namespace StructuralExhaustion.Graph.LongPrefixDegreeRefinement

open StructuralExhaustion

universe u

/-!
# Exact-degree refinement of an observed long-prefix collision

This is the first dependency-ready consumer of the coarse collision produced
by `LongPrefixObservedLabel`.  It evaluates only the two already retained
literal vertices.  The result either upgrades the collision to equality of
their full ambient degrees or records a genuine unequal pair whose degrees
remain congruent modulo four.  In both cases the exact marked-set bit is also
retained.

No response context, D4--D7 family, state universe, or graph universe is
enumerated.  In particular, this classifier does not authorize CT8 removal.
-/

variable {V : Type u} {object : FiniteObject V}
variable {input : LongPrefixObservedLabel.Input object}

/-- The exact two-occurrence residual supplied by the predecessor. -/
structure Source where
  observed : LongPrefixObservedLabel.SemanticRefinementResidual input

namespace Source

variable (source : Source (input := input))

noncomputable abbrev first : LongPrefixObservedLabel.Occurrence :=
  source.observed.repetition.collision.first

noncomputable abbrev second : LongPrefixObservedLabel.Occurrence :=
  source.observed.repetition.collision.second

noncomputable def firstVertex : V := LongPrefixObservedLabel.vertex input source.first

noncomputable def secondVertex : V := LongPrefixObservedLabel.vertex input source.second

noncomputable def firstDegree : Nat := object.degree source.firstVertex

noncomputable def secondDegree : Nat := object.degree source.secondVertex

theorem occurrences_distinct : source.first ≠ source.second :=
  source.observed.repetition.distinct

theorem sameMarkedBit :
    LongPrefixObservedLabel.markedBit input source.first =
      LongPrefixObservedLabel.markedBit input source.second := by
  exact congrArg Prod.snd source.observed.repetition.sameLabel

theorem degrees_mod_four_equal :
    source.firstDegree % 4 = source.secondDegree % 4 := by
  have residues := congrArg Prod.fst source.observed.repetition.sameLabel
  exact congrArg Fin.val residues

end Source

/-- The coarse collision upgrades to equality of the full observed degrees. -/
structure ExactDegreeResidual (source : Source (input := input)) where
  degreeEqual : source.firstDegree = source.secondDegree
  degreeResidueEqual : source.firstDegree % 4 = source.secondDegree % 4
  markedEqual :
    LongPrefixObservedLabel.markedBit input source.first =
      LongPrefixObservedLabel.markedBit input source.second

/-- The coarse collision hides a genuine degree gap, but its endpoints retain
the exact congruence modulo four forced by the predecessor label. -/
structure CongruentDegreeGapResidual (source : Source (input := input)) where
  degreeNotEqual : source.firstDegree ≠ source.secondDegree
  degreeResidueEqual : source.firstDegree % 4 = source.secondDegree % 4
  markedEqual :
    LongPrefixObservedLabel.markedBit input source.first =
      LongPrefixObservedLabel.markedBit input source.second

inductive Result (source : Source (input := input)) where
  | exactDegree (residual : ExactDegreeResidual source)
  | congruentDegreeGap (residual : CongruentDegreeGapResidual source)

/-- One equality decision on the two literal degrees. -/
noncomputable def run (source : Source (input := input)) : Result source := by
  classical
  by_cases equal : source.firstDegree = source.secondDegree
  · exact .exactDegree
      ⟨equal, source.degrees_mod_four_equal, source.sameMarkedBit⟩
  · exact .congruentDegreeGap
      ⟨equal, source.degrees_mod_four_equal, source.sameMarkedBit⟩

theorem run_eq_exactDegree (source : Source (input := input))
    (equal : source.firstDegree = source.secondDegree) :
    ∃ residual, run source = .exactDegree residual := by
  let residual : ExactDegreeResidual source :=
    ⟨equal, source.degrees_mod_four_equal, source.sameMarkedBit⟩
  refine ⟨residual, ?_⟩
  simp [run, equal]

theorem run_eq_congruentDegreeGap (source : Source (input := input))
    (different : source.firstDegree ≠ source.secondDegree) :
    ∃ residual, run source = .congruentDegreeGap residual := by
  let residual : CongruentDegreeGapResidual source :=
    ⟨different, source.degrees_mod_four_equal, source.sameMarkedBit⟩
  refine ⟨residual, ?_⟩
  simp [run, different]

theorem run_exhaustive (source : Source (input := input)) :
    (∃ residual, run source = .exactDegree residual) ∨
      (∃ residual, run source = .congruentDegreeGap residual) := by
  cases equation : run source with
  | exactDegree residual => exact Or.inl ⟨residual, rfl⟩
  | congruentDegreeGap residual => exact Or.inr ⟨residual, rfl⟩

theorem source_occurrences_distinct (source : Source (input := input)) :
    source.first ≠ source.second := source.occurrences_distinct

/-- Computing two degrees scans the declared finite vertex order twice; the
final equality comparison contributes one primitive check. -/
def visibleChecks : Nat := 2 * object.input.vertices.card + 1

theorem visibleChecks_le :
    visibleChecks (object := object) ≤ 2 * (object.input.vertices.card + 1) := by
  unfold visibleChecks
  omega

end StructuralExhaustion.Graph.LongPrefixDegreeRefinement
