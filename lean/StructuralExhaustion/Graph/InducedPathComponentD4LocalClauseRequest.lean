import StructuralExhaustion.Graph.InducedPathComponentD4D7ClauseCursor

namespace StructuralExhaustion.Graph.InducedPathComponentD4LocalClauseRequest

open StructuralExhaustion

universe u uMarker

/-!
# Local request for the focused D4 clause

The cursor supplies a literal slot and an exact dependent marker, but no
predicate evaluating that slot.  The only unconditional consumer is therefore
a typed local request.  It inspects the singleton focused schedule and leaves
the tail untouched; it does not accept a caller-authored Boolean.
-/

namespace PreviousCursor
export InducedPathComponentD4D7ClauseCursor (Cursor Refined)
end PreviousCursor

namespace Schedule
export InducedPathComponentD4D7ClauseSchedule (ClauseSlot Ledger Scheduled)
end Schedule

/-- One exact local D4 evaluation request.  `slots` is deliberately a
singleton, not an enumeration of possible clauses or responses. -/
structure Request {Marker : Type uMarker} {source : Nonempty Marker}
    {ledger : Schedule.Ledger source} (focused : PreviousCursor.Cursor ledger) where
  marker : Nonempty Marker
  markerExact : marker = focused.marker
  slots : List Schedule.ClauseSlot
  slotsExact : slots = [focused.current]
  slotIsD4 : focused.current = .d4
  tail : List Schedule.ClauseSlot
  tailExact : tail = focused.remaining
  tailIsD5D7 : tail = [.d5, .d6, .d7]

def request {Marker : Type uMarker} {source : Nonempty Marker}
    {ledger : Schedule.Ledger source} (focused : PreviousCursor.Cursor ledger) :
    Request focused where
  marker := focused.marker
  markerExact := rfl
  slots := [focused.current]
  slotsExact := rfl
  slotIsD4 := focused.currentExact
  tail := focused.remaining
  tailExact := rfl
  tailIsD5D7 := focused.remainingExact

@[simp] theorem request_slots_length {Marker : Type uMarker}
    {source : Nonempty Marker} {ledger : Schedule.Ledger source}
    (focused : PreviousCursor.Cursor ledger) :
    (request focused).slots.length = 1 := rfl

variable {V : Type u} {object : FiniteObject V}
variable
  (input : InducedPathComponentD1D3Ledger.Input object)
  (anchorState : InducedPathComponentD1D3Ledger.State)
  (LengthOK : Nat → Prop)
  (lengthOKDecidable : DecidablePred LengthOK)

namespace Readiness
export InducedPathComponentD4D7SemanticReadiness (CoarseBlocked BoundedBlocked Result)
end Readiness

/-- A request for each exact cursor occurrence produced by node 185. -/
inductive Requested :
    {source : Readiness.Result input anchorState LengthOK lengthOKDecidable} →
    {scheduled : Schedule.Scheduled input anchorState LengthOK
      lengthOKDecidable source} →
    PreviousCursor.Refined input anchorState LengthOK lengthOKDecidable scheduled →
    Type (u + 1) where
  | coarse
      {blocked : Readiness.CoarseBlocked input anchorState LengthOK
        lengthOKDecidable}
      {first : Schedule.Ledger blocked.firstMissing}
      {second : Schedule.Ledger blocked.secondMissing}
      {firstCursor : PreviousCursor.Cursor first}
      {secondCursor : PreviousCursor.Cursor second}
      (firstRequest : Request firstCursor)
      (secondRequest : Request secondCursor) :
      Requested (.coarse firstCursor secondCursor)
  | bounded
      {blocked : Readiness.BoundedBlocked input anchorState LengthOK
        lengthOKDecidable}
      {only : Schedule.Ledger blocked.missing}
      {onlyCursor : PreviousCursor.Cursor only}
      (onlyRequest : Request onlyCursor) : Requested (.bounded onlyCursor)

def run
    {source : Readiness.Result input anchorState LengthOK lengthOKDecidable}
    {scheduled : Schedule.Scheduled input anchorState LengthOK
      lengthOKDecidable source}
    (refined : PreviousCursor.Refined input anchorState LengthOK lengthOKDecidable
      scheduled) :
    Requested input anchorState LengthOK lengthOKDecidable refined := by
  cases refined with
  | coarse firstCursor secondCursor =>
      exact .coarse (request firstCursor) (request secondCursor)
  | bounded onlyCursor => exact .bounded (request onlyCursor)

theorem run_total
    {source : Readiness.Result input anchorState LengthOK lengthOKDecidable}
    {scheduled : Schedule.Scheduled input anchorState LengthOK
      lengthOKDecidable source}
    (refined : PreviousCursor.Refined input anchorState LengthOK lengthOKDecidable
      scheduled) :
    Nonempty (Requested input anchorState LengthOK lengthOKDecidable refined) :=
  ⟨run input anchorState LengthOK lengthOKDecidable refined⟩

/-- At most two actual marker occurrences can request the singleton D4 slot. -/
def requestedSlots
    {source : Readiness.Result input anchorState LengthOK lengthOKDecidable}
    {scheduled : Schedule.Scheduled input anchorState LengthOK
      lengthOKDecidable source}
    (refined : PreviousCursor.Refined input anchorState LengthOK lengthOKDecidable
      scheduled) : Nat :=
  match refined with
  | .coarse _ _ => 2
  | .bounded _ => 1

theorem requestedSlots_le_two
    {source : Readiness.Result input anchorState LengthOK lengthOKDecidable}
    {scheduled : Schedule.Scheduled input anchorState LengthOK
      lengthOKDecidable source}
    (refined : PreviousCursor.Refined input anchorState LengthOK lengthOKDecidable
      scheduled) :
    requestedSlots input anchorState LengthOK lengthOKDecidable refined ≤ 2 := by
  cases refined <;> simp [requestedSlots]

end StructuralExhaustion.Graph.InducedPathComponentD4LocalClauseRequest
