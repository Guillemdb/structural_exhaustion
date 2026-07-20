import StructuralExhaustion.Core.ChunkedFiniteCount
import Mathlib.Tactic

namespace StructuralExhaustion.Examples.ChunkedFiniteCount

open Core

/-- Non-problem-specific fixture: chunking preserves the exact count of true
entries in the canonical Boolean enumeration. -/
theorem bool_true_count :
    Core.ChunkedFiniteCount.chunkedCount id 1 2
      Core.Enumeration.bool.orderedValues = 1 := by
  decide

/-- The generic cardinal bridge identifies the singleton accepted subtype. -/
theorem bool_true_subtype_count :
    (Core.Enumeration.subtype Core.Enumeration.bool
      (fun value => value = true) (fun value => inferInstance)).card = 1 := by
  rw [Core.ChunkedFiniteCount.subtype_card_eq_chunkedCount
    Core.Enumeration.bool (fun value => value = true)
      (fun value => inferInstance) id (by intro value; rfl)]
  exact bool_true_count

/-- Independent certificates for two width-two intervals and a width-one
tail compose to the exact five-entry sum. -/
def fiveEntryValue (index : Fin 5) : Nat := index.1 + 1

theorem five_entry_certified_intervals :
    (∑ index : Fin 5, fiveEntryValue index) = 15 := by
  have composed :=
    Core.ChunkedFiniteCount.finSum_eq_certifiedIntervals_add_tail
      fiveEntryValue (fun chunk => 4 * chunk + 3)
      2 5
      (by
        intro chunk chunk_mem
        simp only [Finset.mem_range] at chunk_mem
        interval_cases chunk <;> decide)
      (by decide)
  norm_num at composed
  exact composed

/-- A `3 × 5` all-one table is assembled from independently certified
`2 × 2` rectangles, the two boundary strips, and the corner. -/
theorem three_by_five_certified_rectangles :
    (∑ _row : Fin 3, ∑ _column : Fin 5, 1) = 15 := by
  have composed :=
    Core.ChunkedFiniteCount.finDoubleSum_eq_certifiedRectangles_add_tails
      (fun _row : Fin 3 => fun _column : Fin 5 => 1) 2 2
      (fun _rowChunk _columnChunk => 4)
      (fun _columnChunk => 2)
      (fun _rowChunk => 2)
      1
      (by
        intro rowChunk rowChunk_mem columnChunk columnChunk_mem
        simp only [Finset.mem_range] at rowChunk_mem columnChunk_mem
        interval_cases rowChunk <;> interval_cases columnChunk <;> decide)
      (by
        intro columnChunk columnChunk_mem
        simp only [Finset.mem_range] at columnChunk_mem
        interval_cases columnChunk <;> decide)
      (by
        intro rowChunk rowChunk_mem
        simp only [Finset.mem_range] at rowChunk_mem
        interval_cases rowChunk <;> decide)
      (by decide)
  norm_num at composed ⊢

#print axioms bool_true_count
#print axioms bool_true_subtype_count
#print axioms five_entry_certified_intervals
#print axioms three_by_five_certified_rectangles

end StructuralExhaustion.Examples.ChunkedFiniteCount
