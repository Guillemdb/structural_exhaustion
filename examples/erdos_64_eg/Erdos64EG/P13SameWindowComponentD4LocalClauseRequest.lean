import Erdos64EG.P13SameWindowComponentD4D7ClauseCursor
import StructuralExhaustion.Graph.InducedPathComponentD4LocalClauseRequest

namespace Erdos64EG.Internal

open StructuralExhaustion
open StructuralExhaustion.Graph

universe u

/-!
# Node [188]: exact local request for the focused D4 obligation

The exact node-185 cursor contains a D4 slot but no predicate assigning that
slot a truth value.  This node consumes that cursor and emits one singleton
local evaluation request per actual marker occurrence.  It preserves the
D5--D7 tail and does not accept a Boolean, enumerate contexts, or execute CT8.
Genuine graph-derived semantics remain the sole successor obligation [191].
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
variable (source185 : transition.D4D7ClauseCursorSource source174 source175
  source180 source182)

structure D4LocalClauseRequestSource where
  node185 : transition.D4D7ClauseCursorOutput source174
  node185Exact : node185 = transition.runD4D7ClauseCursor source174 source175
    source180 source182 source185

noncomputable def computedD4LocalClauseRequestSource :
    transition.D4LocalClauseRequestSource source174 source175 source180
      source182 source185 where
  node185 := transition.runD4D7ClauseCursor source174 source175 source180
    source182 source185
  node185Exact := rfl

inductive D4LocalClauseRequestOutput where
  | coarse
      (blocked : transition.D4D7CoarseSemanticBlock source174)
      (first : InducedPathComponentD4D7ClauseSchedule.Ledger
        blocked.firstMissing)
      (second : InducedPathComponentD4D7ClauseSchedule.Ledger
        blocked.secondMissing)
      (firstCursor : InducedPathComponentD4D7ClauseCursor.Cursor first)
      (secondCursor : InducedPathComponentD4D7ClauseCursor.Cursor second)
      (firstRequest : InducedPathComponentD4LocalClauseRequest.Request firstCursor)
      (secondRequest :
        InducedPathComponentD4LocalClauseRequest.Request secondCursor)
  | bounded
      (blocked : transition.D4D7BoundedSemanticBlock source174)
      (only : InducedPathComponentD4D7ClauseSchedule.Ledger blocked.missing)
      (onlyCursor : InducedPathComponentD4D7ClauseCursor.Cursor only)
      (onlyRequest : InducedPathComponentD4LocalClauseRequest.Request onlyCursor)

noncomputable def runD4LocalClauseRequest
    (source188 : transition.D4LocalClauseRequestSource source174 source175
      source180 source182 source185) :
    transition.D4LocalClauseRequestOutput source174 := by
  cases source188.node185 with
  | coarse blocked first second firstCursor secondCursor =>
      exact .coarse blocked first second firstCursor secondCursor
        (InducedPathComponentD4LocalClauseRequest.request firstCursor)
        (InducedPathComponentD4LocalClauseRequest.request secondCursor)
  | bounded blocked only onlyCursor =>
      exact .bounded blocked only onlyCursor
        (InducedPathComponentD4LocalClauseRequest.request onlyCursor)

theorem d4LocalClauseRequest_exact_node185
    (source188 : transition.D4LocalClauseRequestSource source174 source175
      source180 source182 source185) :
    source188.node185 = transition.runD4D7ClauseCursor source174 source175
      source180 source182 source185 := source188.node185Exact

theorem runD4LocalClauseRequest_exhaustive
    (source188 : transition.D4LocalClauseRequestSource source174 source175
      source180 source182 source185) :
    (∃ blocked first second firstCursor secondCursor firstRequest secondRequest,
      transition.runD4LocalClauseRequest source174 source175 source180 source182
        source185 source188 = .coarse blocked first second firstCursor
          secondCursor firstRequest secondRequest) ∨
    (∃ blocked only onlyCursor onlyRequest,
      transition.runD4LocalClauseRequest source174 source175 source180 source182
        source185 source188 = .bounded blocked only onlyCursor onlyRequest) := by
  cases equation : transition.runD4LocalClauseRequest source174 source175
      source180 source182 source185 source188 with
  | coarse blocked first second firstCursor secondCursor firstRequest secondRequest =>
      exact Or.inl ⟨blocked, first, second, firstCursor, secondCursor,
        firstRequest, secondRequest, rfl⟩
  | bounded blocked only onlyCursor onlyRequest =>
      exact Or.inr ⟨blocked, only, onlyCursor, onlyRequest, rfl⟩

/-- Literal singleton request slots in the concrete returned output. -/
def D4LocalClauseRequestOutput.requestedSlots :
    transition.D4LocalClauseRequestOutput source174 → Nat
  | .coarse _ _ _ _ _ firstRequest secondRequest =>
      firstRequest.slots.length + secondRequest.slots.length
  | .bounded _ _ _ onlyRequest => onlyRequest.slots.length

theorem runD4LocalClauseRequest_requestedSlots_le_two
    (source188 : transition.D4LocalClauseRequestSource source174 source175
      source180 source182 source185) :
    (transition.runD4LocalClauseRequest source174 source175 source180 source182
      source185 source188).requestedSlots ≤ 2 := by
  rcases source188 with ⟨node185, node185Exact⟩
  cases node185 <;>
    simp [runD4LocalClauseRequest, D4LocalClauseRequestOutput.requestedSlots,
      InducedPathComponentD4LocalClauseRequest.request]

theorem exists_verifiedD4LocalClauseRequestPrefix :
    ∃ output, output = transition.runD4LocalClauseRequest source174 source175
      source180 source182 source185
      (transition.computedD4LocalClauseRequestSource source174 source175
        source180 source182 source185) ∧
      ((∃ blocked first second firstCursor secondCursor firstRequest secondRequest,
          output = .coarse blocked first second firstCursor secondCursor
            firstRequest secondRequest) ∨
        (∃ blocked only onlyCursor onlyRequest,
          output = .bounded blocked only onlyCursor onlyRequest)) := by
  refine ⟨_, rfl, ?_⟩
  exact transition.runD4LocalClauseRequest_exhaustive source174 source175
    source180 source182 source185 _

end P13SameWindowFirstTransitionBoundaryInput

end Erdos64EG.Internal
