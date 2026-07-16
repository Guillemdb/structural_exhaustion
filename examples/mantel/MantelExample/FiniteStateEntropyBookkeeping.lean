import MantelExample.Concrete
import StructuralExhaustion.Core.FiniteStateEntropyBookkeeping

namespace MantelExample.FiniteStateEntropyBookkeeping

open StructuralExhaustion

/-!
# Exact local state bookkeeping on `C₅`

The states below are the five vertices already supplied by the concrete
triangle-free `C₅` input.  The Core profile consumes that named collection
directly; it does not enumerate graphs, subsets, assignments, or an ambient
vertex type.
-/

/-- Local state bookkeeping for the actual vertex collection of the concrete
Mantel `C₅`. -/
def profile : Core.FiniteStateEntropyBookkeeping.Profile where
  State := ConcreteC5.Vertex
  states := ConcreteC5.object.input.vertices.toOrderedCollection
  supportSize := ConcreteC5.object.input.vertices.card

/-- The supplied graph-state collection has exactly five entries. -/
theorem stateCount_exact : profile.stateCount = 5 := by
  native_decide

/-- Its integer floor-logarithmic bit count is exactly two. -/
theorem bitCount_exact : profile.bitCount = 2 := by
  native_decide

/-- The recorded support is the same concrete five-vertex support. -/
theorem supportSize_exact : profile.supportSize = 5 := by
  native_decide

/-- Its real normalized entropy is the literal manuscript expression on the
same five supplied graph states. -/
theorem normalizedEntropy_exact :
    profile.normalizedEntropy = Real.logb 2 5 / 5 := by
  rw [profile.normalizedEntropy_eq, stateCount_exact, supportSize_exact]
  norm_num

/-- Bookkeeping itself performs no semantic predicate call on graph states. -/
theorem semanticChecks_exact : profile.semanticChecks = 0 :=
  profile.semanticChecks_eq_zero

/-- Length/logarithm evaluation obeys the Core linear local bound. -/
theorem arithmeticWork_le_eleven : profile.arithmeticWork ≤ 11 := by
  calc
    profile.arithmeticWork ≤ 2 * profile.stateCount + 1 :=
      profile.arithmeticWork_le_two_mul_stateCount_add_one
    _ = 11 := by rw [stateCount_exact]

/-- The transfer uses the very same graph object already proved triangle-free
in the external Mantel package. -/
theorem source_triangleFree : ConcreteC5.object.graph.CliqueFree 3 :=
  ConcreteC5.triangleFree

end MantelExample.FiniteStateEntropyBookkeeping
