import StructuralExhaustion.Graph.InducedPathComponentD4LocalClauseRequest

namespace StructuralExhaustion.Graph.InducedPathComponentD4EvaluatorResidual

open StructuralExhaustion

universe u uMarker

/-! # Missing graph-owned evaluator for a local D4 request

The predecessor supplies a singleton D4 request but no predicate.  This module
records the two inputs an honest evaluator must provide.  It contains no truth
value and cannot be used as a caller-authored evaluator.
-/

namespace PreviousRequest
export InducedPathComponentD4LocalClauseRequest (Request Requested)
end PreviousRequest

namespace PreviousCursor
export InducedPathComponentD4D7ClauseCursor (Cursor Refined)
end PreviousCursor

namespace Schedule
export InducedPathComponentD4D7ClauseSchedule (Ledger Scheduled)
end Schedule

inductive Requirement
  | graphLocalPredicate
  | predicateProvenance
  deriving DecidableEq, Repr

def requirements : List Requirement :=
  [.graphLocalPredicate, .predicateProvenance]

theorem requirements_nodup : requirements.Nodup := by decide

/-- Exact pending evaluator contract.  The absence of a `Bool` field is
intentional: the eventual predicate and its correctness must be graph-owned. -/
structure Residual {Marker : Type uMarker} {source : Nonempty Marker}
    {ledger : Schedule.Ledger source} {focused : PreviousCursor.Cursor ledger}
    (pending : PreviousRequest.Request focused) where
  marker : Nonempty Marker
  markerExact : marker = pending.marker
  slots : List InducedPathComponentD4D7ClauseSchedule.ClauseSlot
  slotsExact : slots = pending.slots
  needs : List Requirement
  needsExact : needs = requirements
  needsNodup : needs.Nodup
  tail : List InducedPathComponentD4D7ClauseSchedule.ClauseSlot
  tailExact : tail = pending.tail

def residual {Marker : Type uMarker} {source : Nonempty Marker}
    {ledger : Schedule.Ledger source} {focused : PreviousCursor.Cursor ledger}
    (pending : PreviousRequest.Request focused) : Residual pending where
  marker := pending.marker
  markerExact := rfl
  slots := pending.slots
  slotsExact := rfl
  needs := requirements
  needsExact := rfl
  needsNodup := requirements_nodup
  tail := pending.tail
  tailExact := rfl

@[simp] theorem residual_needs_length {Marker : Type uMarker}
    {source : Nonempty Marker} {ledger : Schedule.Ledger source}
    {focused : PreviousCursor.Cursor ledger}
    (pending : PreviousRequest.Request focused) :
    (residual pending).needs.length = 2 := rfl

variable {V : Type u} {object : FiniteObject V}
variable
  (input : InducedPathComponentD1D3Ledger.Input object)
  (anchorState : InducedPathComponentD1D3Ledger.State)
  (LengthOK : Nat → Prop)
  (lengthOKDecidable : DecidablePred LengthOK)

namespace Readiness
export InducedPathComponentD4D7SemanticReadiness (CoarseBlocked BoundedBlocked Result)
end Readiness

inductive Exposed :
    {source : Readiness.Result input anchorState LengthOK lengthOKDecidable} →
    {scheduled : Schedule.Scheduled input anchorState LengthOK
      lengthOKDecidable source} →
    {refined : PreviousCursor.Refined input anchorState LengthOK lengthOKDecidable
      scheduled} →
    PreviousRequest.Requested input anchorState LengthOK lengthOKDecidable refined →
    Type (u + 1) where
  | coarse
      {blocked : Readiness.CoarseBlocked input anchorState LengthOK
        lengthOKDecidable}
      {first : Schedule.Ledger blocked.firstMissing}
      {second : Schedule.Ledger blocked.secondMissing}
      {firstCursor : PreviousCursor.Cursor first}
      {secondCursor : PreviousCursor.Cursor second}
      {firstRequest : PreviousRequest.Request firstCursor}
      {secondRequest : PreviousRequest.Request secondCursor}
      (firstResidual : Residual firstRequest)
      (secondResidual : Residual secondRequest) :
      Exposed (.coarse firstRequest secondRequest)
  | bounded
      {blocked : Readiness.BoundedBlocked input anchorState LengthOK
        lengthOKDecidable}
      {only : Schedule.Ledger blocked.missing}
      {onlyCursor : PreviousCursor.Cursor only}
      {onlyRequest : PreviousRequest.Request onlyCursor}
      (onlyResidual : Residual onlyRequest) : Exposed (.bounded onlyRequest)

def run
    {source : Readiness.Result input anchorState LengthOK lengthOKDecidable}
    {scheduled : Schedule.Scheduled input anchorState LengthOK
      lengthOKDecidable source}
    {refined : PreviousCursor.Refined input anchorState LengthOK lengthOKDecidable
      scheduled}
    (requested : PreviousRequest.Requested input anchorState LengthOK lengthOKDecidable
      refined) :
    Exposed input anchorState LengthOK lengthOKDecidable requested := by
  cases requested with
  | coarse firstRequest secondRequest =>
      exact .coarse (residual firstRequest) (residual secondRequest)
  | bounded onlyRequest => exact .bounded (residual onlyRequest)

theorem run_total
    {source : Readiness.Result input anchorState LengthOK lengthOKDecidable}
    {scheduled : Schedule.Scheduled input anchorState LengthOK
      lengthOKDecidable source}
    {refined : PreviousCursor.Refined input anchorState LengthOK lengthOKDecidable
      scheduled}
    (requested : PreviousRequest.Requested input anchorState LengthOK lengthOKDecidable
      refined) : Nonempty
      (Exposed input anchorState LengthOK lengthOKDecidable requested) :=
  ⟨run input anchorState LengthOK lengthOKDecidable requested⟩

def requiredInputs
    {source : Readiness.Result input anchorState LengthOK lengthOKDecidable}
    {scheduled : Schedule.Scheduled input anchorState LengthOK
      lengthOKDecidable source}
    {refined : PreviousCursor.Refined input anchorState LengthOK lengthOKDecidable
      scheduled}
    (requested : PreviousRequest.Requested input anchorState LengthOK lengthOKDecidable
      refined) : Nat := match requested with | .coarse _ _ => 4 | .bounded _ => 2

theorem requiredInputs_le_four
    {source : Readiness.Result input anchorState LengthOK lengthOKDecidable}
    {scheduled : Schedule.Scheduled input anchorState LengthOK
      lengthOKDecidable source}
    {refined : PreviousCursor.Refined input anchorState LengthOK lengthOKDecidable
      scheduled}
    (requested : PreviousRequest.Requested input anchorState LengthOK lengthOKDecidable
      refined) : requiredInputs input anchorState LengthOK lengthOKDecidable
      requested ≤ 4 := by
  cases requested <;> simp [requiredInputs]

end StructuralExhaustion.Graph.InducedPathComponentD4EvaluatorResidual
