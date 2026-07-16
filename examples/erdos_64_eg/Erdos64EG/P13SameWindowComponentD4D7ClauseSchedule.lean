import Erdos64EG.P13SameWindowComponentD4D7SemanticReadiness
import StructuralExhaustion.Graph.InducedPathComponentD4D7ClauseSchedule

namespace Erdos64EG.Internal

open StructuralExhaustion
open StructuralExhaustion.Graph

universe u

/-!
# Node [182]: exact finite D4--D7 clause schedule

The node-180 marker has no clause values.  This node retains each dependent
marker and emits only the fixed D4--D7 obligation order.  It proves no clause,
response equivalence, removal operation, or CT8 result.
-/

variable {ctx : Core.MinimalCounterexampleContext
  PackedProblem.{u} PackedTarget.{u}}
variable {previous : VerifiedP13MultiScaleCurvaturePrefix ctx}
variable {window : P13ActualSelectedWindow ctx}
variable {fork : P13ActualAttachmentColdFork ctx previous window}
variable {quiet : P13SameWindowQuietOutput fork}
variable {short : P13SameWindowComputedShort fork quiet}
variable {input : P13SameWindowNormalizedBoundaryInput (short := short)}
variable {computed : P13SameWindowComputedNormalizedReturnBoundary input}

namespace P13SameWindowFirstTransitionBoundaryInput

variable (transition : P13SameWindowFirstTransitionBoundaryInput computed)
variable (source174 : P13SameWindowComponentD1D3LedgerSource transition)
variable (source175 :
  P13SameWindowComponentD4D7OrCoarseRepeatSource transition source174)
variable (source180 : transition.D4D7SemanticReadinessSource source174 source175)

structure D4D7ClauseScheduleSource where
  node180 : transition.D4D7SemanticReadinessOutput source174
  node180Exact : node180 =
    transition.runD4D7SemanticReadiness source174 source175 source180

noncomputable def computedD4D7ClauseScheduleSource :
    transition.D4D7ClauseScheduleSource source174 source175 source180 where
  node180 := transition.runD4D7SemanticReadiness source174 source175 source180
  node180Exact := rfl

inductive D4D7ClauseScheduleOutput where
  | coarse
      (blocked : transition.D4D7CoarseSemanticBlock source174)
      (first : InducedPathComponentD4D7ClauseSchedule.Ledger
        blocked.firstMissing)
      (second : InducedPathComponentD4D7ClauseSchedule.Ledger
        blocked.secondMissing)
  | bounded
      (blocked : transition.D4D7BoundedSemanticBlock source174)
      (only : InducedPathComponentD4D7ClauseSchedule.Ledger blocked.missing)

noncomputable def runD4D7ClauseSchedule
    (source182 : transition.D4D7ClauseScheduleSource source174 source175 source180) :
    transition.D4D7ClauseScheduleOutput source174 := by
  cases source182.node180 with
  | coarseBlocked blocked =>
      exact .coarse blocked
        (InducedPathComponentD4D7ClauseSchedule.ledger blocked.firstMissing)
        (InducedPathComponentD4D7ClauseSchedule.ledger blocked.secondMissing)
  | boundedBlocked blocked =>
      exact .bounded blocked
        (InducedPathComponentD4D7ClauseSchedule.ledger blocked.missing)

theorem d4d7ClauseSchedule_exact_node180
    (source182 : transition.D4D7ClauseScheduleSource source174 source175 source180) :
    source182.node180 =
      transition.runD4D7SemanticReadiness source174 source175 source180 :=
  source182.node180Exact

theorem runD4D7ClauseSchedule_exhaustive
    (source182 : transition.D4D7ClauseScheduleSource source174 source175 source180) :
    (∃ blocked first second,
      transition.runD4D7ClauseSchedule source174 source175 source180 source182 =
        .coarse blocked first second) ∨
    (∃ blocked only,
      transition.runD4D7ClauseSchedule source174 source175 source180 source182 =
        .bounded blocked only) := by
  cases equation : transition.runD4D7ClauseSchedule source174 source175
      source180 source182 with
  | coarse blocked first second => exact Or.inl ⟨blocked, first, second, rfl⟩
  | bounded blocked only => exact Or.inr ⟨blocked, only, rfl⟩

/-- The number of literal fixed slots retained by one concrete output. -/
def D4D7ClauseScheduleOutput.emittedSlots :
    transition.D4D7ClauseScheduleOutput source174 → Nat
  | .coarse _ first second => first.slots.length + second.slots.length
  | .bounded _ only => only.slots.length

theorem runD4D7ClauseSchedule_emittedSlots_le_eight
    (source182 : transition.D4D7ClauseScheduleSource source174 source175 source180) :
    (transition.runD4D7ClauseSchedule source174 source175 source180 source182
      ).emittedSlots ≤ 8 := by
  rcases source182 with ⟨node180, node180Exact⟩
  cases node180 <;>
    simp [runD4D7ClauseSchedule, D4D7ClauseScheduleOutput.emittedSlots]

theorem exists_verifiedD4D7ClauseSchedulePrefix :
    ∃ output, output = transition.runD4D7ClauseSchedule source174 source175
      source180 (transition.computedD4D7ClauseScheduleSource source174 source175
        source180) ∧
      ((∃ blocked first second, output = .coarse blocked first second) ∨
        (∃ blocked only, output = .bounded blocked only)) := by
  refine ⟨_, rfl, ?_⟩
  exact transition.runD4D7ClauseSchedule_exhaustive source174 source175
    source180 _

end P13SameWindowFirstTransitionBoundaryInput

end Erdos64EG.Internal
