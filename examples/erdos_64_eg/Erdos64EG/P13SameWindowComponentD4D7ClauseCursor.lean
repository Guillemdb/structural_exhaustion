import Erdos64EG.P13SameWindowComponentD4D7ClauseSchedule
import StructuralExhaustion.Graph.InducedPathComponentD4D7ClauseCursor

namespace Erdos64EG.Internal

open StructuralExhaustion
open StructuralExhaustion.Graph

universe u

/-!
# Node [185]: focus the first unresolved D4--D7 obligation

Node 182 supplies exact fixed obligation ledgers, but its markers carry no
clause truth.  This node only focuses D4 as the next obligation and retains
D5--D7 as the exact unevaluated tail.  It does not construct a response map,
compatible context, smaller object, or CT8 certificate.
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
variable (source182 :
  transition.D4D7ClauseScheduleSource source174 source175 source180)

structure D4D7ClauseCursorSource where
  node182 : transition.D4D7ClauseScheduleOutput source174
  node182Exact : node182 = transition.runD4D7ClauseSchedule source174 source175
    source180 source182

noncomputable def computedD4D7ClauseCursorSource :
    transition.D4D7ClauseCursorSource source174 source175 source180 source182 where
  node182 := transition.runD4D7ClauseSchedule source174 source175 source180 source182
  node182Exact := rfl

inductive D4D7ClauseCursorOutput where
  | coarse
      (blocked : transition.D4D7CoarseSemanticBlock source174)
      (first : InducedPathComponentD4D7ClauseSchedule.Ledger
        blocked.firstMissing)
      (second : InducedPathComponentD4D7ClauseSchedule.Ledger
        blocked.secondMissing)
      (firstCursor : InducedPathComponentD4D7ClauseCursor.Cursor first)
      (secondCursor : InducedPathComponentD4D7ClauseCursor.Cursor second)
  | bounded
      (blocked : transition.D4D7BoundedSemanticBlock source174)
      (only : InducedPathComponentD4D7ClauseSchedule.Ledger blocked.missing)
      (onlyCursor : InducedPathComponentD4D7ClauseCursor.Cursor only)

noncomputable def runD4D7ClauseCursor
    (source185 : transition.D4D7ClauseCursorSource source174 source175 source180
      source182) : transition.D4D7ClauseCursorOutput source174 := by
  cases source185.node182 with
  | coarse blocked first second =>
      exact .coarse blocked first second
        (InducedPathComponentD4D7ClauseCursor.cursor first)
        (InducedPathComponentD4D7ClauseCursor.cursor second)
  | bounded blocked only =>
      exact .bounded blocked only
        (InducedPathComponentD4D7ClauseCursor.cursor only)

theorem d4d7ClauseCursor_exact_node182
    (source185 : transition.D4D7ClauseCursorSource source174 source175 source180
      source182) :
    source185.node182 = transition.runD4D7ClauseSchedule source174 source175
      source180 source182 := source185.node182Exact

theorem runD4D7ClauseCursor_exhaustive
    (source185 : transition.D4D7ClauseCursorSource source174 source175 source180
      source182) :
    (∃ blocked first second firstCursor secondCursor,
      transition.runD4D7ClauseCursor source174 source175 source180 source182
        source185 = .coarse blocked first second firstCursor secondCursor) ∨
    (∃ blocked only onlyCursor,
      transition.runD4D7ClauseCursor source174 source175 source180 source182
        source185 = .bounded blocked only onlyCursor) := by
  cases equation : transition.runD4D7ClauseCursor source174 source175 source180
      source182 source185 with
  | coarse blocked first second firstCursor secondCursor =>
      exact Or.inl ⟨blocked, first, second, firstCursor, secondCursor, rfl⟩
  | bounded blocked only onlyCursor =>
      exact Or.inr ⟨blocked, only, onlyCursor, rfl⟩

/-- Actual unevaluated tail slots retained by a concrete output. -/
def D4D7ClauseCursorOutput.remainingSlots :
    transition.D4D7ClauseCursorOutput source174 → Nat
  | .coarse _ _ _ firstCursor secondCursor =>
      firstCursor.remaining.length + secondCursor.remaining.length
  | .bounded _ _ onlyCursor => onlyCursor.remaining.length

theorem runD4D7ClauseCursor_remainingSlots_le_six
    (source185 : transition.D4D7ClauseCursorSource source174 source175 source180
      source182) :
    (transition.runD4D7ClauseCursor source174 source175 source180 source182
      source185).remainingSlots ≤ 6 := by
  rcases source185 with ⟨node182, node182Exact⟩
  cases node182 <;>
    simp [runD4D7ClauseCursor, D4D7ClauseCursorOutput.remainingSlots,
      InducedPathComponentD4D7ClauseCursor.cursor]

theorem exists_verifiedD4D7ClauseCursorPrefix :
    ∃ output, output = transition.runD4D7ClauseCursor source174 source175
      source180 source182 (transition.computedD4D7ClauseCursorSource source174
        source175 source180 source182) ∧
      ((∃ blocked first second firstCursor secondCursor,
          output = .coarse blocked first second firstCursor secondCursor) ∨
        (∃ blocked only onlyCursor,
          output = .bounded blocked only onlyCursor)) := by
  refine ⟨_, rfl, ?_⟩
  exact transition.runD4D7ClauseCursor_exhaustive source174 source175 source180
    source182 _

end P13SameWindowFirstTransitionBoundaryInput

end Erdos64EG.Internal
