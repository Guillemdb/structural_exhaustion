import Erdos64EG.CT10P13MultiScaleCurvature
import StructuralExhaustion.Core.FiniteSequentialFiltration

namespace Erdos64EG.Internal

open StructuralExhaustion
open StructuralExhaustion.Core.FiniteSequentialFiltration

universe uState

set_option maxRecDepth 100000

/-!
# Thin P13 sequential-filtration interface

This file reuses the exact node-[21] safe and flat tables without claiming a
Boolean product.  Given an actual finite graph-owned state universe and its
91 executable barrier tests, the generic runner computes either the complete
retention ledger or the first explicit conditional fibre where the declared
ratio fails.

The still-missing graph producer is deliberately visible in the arguments of
`p13SequentialProfile`: an exact `FinEnum State` and a response-derived test
`P13BarrierIndex → State → Bool`.  Node [21] supplies neither object; it only
supplies the audited weights and compatibility semantics.
-/

def p13SequentialBarrier {State : Type uState}
    (accepts : P13BarrierIndex → State → Bool)
    (index : P13BarrierIndex) : Barrier State where
  accepts := accepts index
  safe := p13BarrierSafeCount index
  flat := p13BarrierFlatCount index

def p13SequentialBarriers {State : Type uState}
    (accepts : P13BarrierIndex → State → Bool) : List (Barrier State) :=
  p13BarrierClassification.classes.orderedValues.map
    (p13SequentialBarrier accepts)

def p13SequentialProfile {State : Type uState}
    (states : FinEnum State)
    (accepts : P13BarrierIndex → State → Bool) : Profile where
  State := State
  states := states
  barriers := p13SequentialBarriers accepts

theorem p13Sequential_safeProduct {State : Type uState}
    (states : FinEnum State)
    (accepts : P13BarrierIndex → State → Bool) :
    (p13SequentialProfile states accepts).safeProduct =
      p13BarrierSafeProduct := by
  rfl

theorem p13Sequential_flatProduct {State : Type uState}
    (states : FinEnum State)
    (accepts : P13BarrierIndex → State → Bool) :
    (p13SequentialProfile states accepts).flatProduct =
      p13BarrierFlatProduct := by
  rfl

/-- The P13 interface is exhaustive without a caller-authored hot/cold flag. -/
theorem p13Sequential_exhaustive {State : Type uState}
    (states : FinEnum State)
    (accepts : P13BarrierIndex → State → Bool) :
    (∃ failure,
        (p13SequentialProfile states accepts).run =
          Outcome.firstFailure failure) ∨
      (∃ ledger,
        (p13SequentialProfile states accepts).run = Outcome.complete ledger) :=
  runFrom_exhaustive _ _

/-- On the complete branch the exact node-[21] products telescope over the
actual finite state filtration. -/
theorem p13Sequential_complete_product_bound {State : Type uState}
    (states : FinEnum State)
    (accepts : P13BarrierIndex → State → Bool)
    (ledger : CompleteLedger states.orderedValues
      (p13SequentialBarriers accepts)) :
    p13BarrierSafeProduct * ledger.finalStates.length ≤
      p13BarrierFlatProduct * states.card := by
  simpa [p13BarrierFlatProduct, p13BarrierSafeProduct,
    p13SequentialBarriers, p13SequentialBarrier, Function.comp_def] using
      ledger.product_le

/-- Node [21]'s strict rate floor remains available on this route, but by
itself it constructs neither states nor graph response tests. -/
theorem p13Sequential_rateFloor
    (ctx : Core.MinimalCounterexampleContext PackedProblem PackedTarget)
    (previous : VerifiedP13MultiScaleCurvaturePrefix ctx) :
    2 ^ 118 * p13BarrierFlatProduct < p13BarrierSafeProduct :=
  previous.rateFloor

theorem p13Sequential_flatProduct_pos : 0 < p13BarrierFlatProduct := by
  apply List.prod_pos
  intro value valueMem
  obtain ⟨index, _indexMem, rfl⟩ := List.mem_map.mp valueMem
  exact (p13Barrier_counts_wellFormed index).1

/-- If the graph-owned filtration reaches a nonempty complete fibre, the
node-[21] rate floor and the telescoping ledger force an exact 118-bit loss.
This is a consequence, not a realization premise. -/
theorem p13Sequential_complete_state_loss
    {State : Type uState}
    (ctx : Core.MinimalCounterexampleContext PackedProblem PackedTarget)
    (previous : VerifiedP13MultiScaleCurvaturePrefix ctx)
    (states : FinEnum State)
    (accepts : P13BarrierIndex → State → Bool)
    (ledger : CompleteLedger states.orderedValues
      (p13SequentialBarriers accepts))
    (finalNonempty : 0 < ledger.finalStates.length) :
    2 ^ 118 * ledger.finalStates.length < states.card := by
  have scaledRate :
      (2 ^ 118 * p13BarrierFlatProduct) * ledger.finalStates.length <
        p13BarrierSafeProduct * ledger.finalStates.length :=
    (Nat.mul_lt_mul_right finalNonempty).2 previous.rateFloor
  have productBound := p13Sequential_complete_product_bound
    states accepts ledger
  have chained :
      (2 ^ 118 * p13BarrierFlatProduct) * ledger.finalStates.length <
        p13BarrierFlatProduct * states.card :=
    lt_of_lt_of_le scaledRate productBound
  apply Nat.lt_of_mul_lt_mul_left (a := p13BarrierFlatProduct)
  simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using chained

end Erdos64EG.Internal
