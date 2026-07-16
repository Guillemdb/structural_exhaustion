import StructuralExhaustion.Graph.InducedPathComponentD4D7ClauseSchedule

namespace StructuralExhaustion.Graph.InducedPathComponentD4D7ClauseCursor

open StructuralExhaustion

universe u uMarker

/-!
# First unresolved D4--D7 obligation

The predecessor schedules four obligations but supplies no clause truth.  This
module therefore performs only the first honest refinement: it focuses the
first scheduled obligation and retains the exact unevaluated tail.  In
particular, `current = d4` means "D4 is next", not that D4 is true or false.
-/

namespace Schedule
export InducedPathComponentD4D7ClauseSchedule
  (ClauseSlot clauseOrder Ledger Scheduled)
end Schedule

/-- A cursor into one exact fixed ledger.  It is purely structural: it carries
no Boolean response or compatible-context assertion. -/
structure Cursor {Marker : Type uMarker} {source : Nonempty Marker}
    (ledger : Schedule.Ledger source) where
  marker : Nonempty Marker
  markerExact : marker = ledger.marker
  current : Schedule.ClauseSlot
  remaining : List Schedule.ClauseSlot
  decomposition : ledger.slots = current :: remaining
  currentExact : current = .d4
  remainingExact : remaining = [.d5, .d6, .d7]
  remainingNodup : remaining.Nodup

def cursor {Marker : Type uMarker} {source : Nonempty Marker}
    (ledger : Schedule.Ledger source) : Cursor ledger where
  marker := ledger.marker
  markerExact := rfl
  current := .d4
  remaining := [.d5, .d6, .d7]
  decomposition := by simp [ledger.slotsExact,
    InducedPathComponentD4D7ClauseSchedule.clauseOrder]
  currentExact := rfl
  remainingExact := rfl
  remainingNodup := by decide

@[simp] theorem cursor_current {Marker : Type uMarker}
    {source : Nonempty Marker} (ledger : Schedule.Ledger source) :
    (cursor ledger).current = .d4 := rfl

@[simp] theorem cursor_remaining {Marker : Type uMarker}
    {source : Nonempty Marker} (ledger : Schedule.Ledger source) :
    (cursor ledger).remaining = [.d5, .d6, .d7] := rfl

variable {V : Type u} {object : FiniteObject V}
variable
  (input : InducedPathComponentD1D3Ledger.Input object)
  (anchorState : InducedPathComponentD1D3Ledger.State)
  (LengthOK : Nat → Prop)
  (lengthOKDecidable : DecidablePred LengthOK)

namespace Previous
export InducedPathComponentD4D7SemanticReadiness (Result)
end Previous

/-- The exact schedule with a cursor for every marker occurrence. -/
inductive Refined : {source : Previous.Result input anchorState LengthOK
      lengthOKDecidable} →
    Schedule.Scheduled input anchorState LengthOK lengthOKDecidable source →
    Type (u + 1) where
  | coarse
      {blocked : InducedPathComponentD4D7SemanticReadiness.CoarseBlocked input
        anchorState LengthOK lengthOKDecidable}
      {first : Schedule.Ledger blocked.firstMissing}
      {second : Schedule.Ledger blocked.secondMissing}
      (firstCursor : Cursor first) (secondCursor : Cursor second) :
      Refined (.coarse first second)
  | bounded
      {blocked : InducedPathComponentD4D7SemanticReadiness.BoundedBlocked input
        anchorState LengthOK lengthOKDecidable}
      {only : Schedule.Ledger blocked.missing}
      (onlyCursor : Cursor only) : Refined (.bounded only)

def run {source : Previous.Result input anchorState LengthOK lengthOKDecidable}
    (scheduled : Schedule.Scheduled input anchorState LengthOK
      lengthOKDecidable source) :
    Refined input anchorState LengthOK lengthOKDecidable scheduled := by
  cases scheduled with
  | coarse first second => exact .coarse (cursor first) (cursor second)
  | bounded only => exact .bounded (cursor only)

theorem run_total
    {source : Previous.Result input anchorState LengthOK lengthOKDecidable}
    (scheduled : Schedule.Scheduled input anchorState LengthOK
      lengthOKDecidable source) :
    Nonempty (Refined input anchorState LengthOK lengthOKDecidable scheduled) :=
  ⟨run input anchorState LengthOK lengthOKDecidable scheduled⟩

/-- Three unevaluated slots remain per actual marker occurrence. -/
def remainingSlots
    {source : Previous.Result input anchorState LengthOK lengthOKDecidable}
    (scheduled : Schedule.Scheduled input anchorState LengthOK
      lengthOKDecidable source) : Nat :=
  match scheduled with
  | .coarse _ _ => 6
  | .bounded _ => 3

theorem remainingSlots_le_six
    {source : Previous.Result input anchorState LengthOK lengthOKDecidable}
    (scheduled : Schedule.Scheduled input anchorState LengthOK
      lengthOKDecidable source) :
    remainingSlots input anchorState LengthOK lengthOKDecidable scheduled ≤ 6 := by
  cases scheduled <;> simp [remainingSlots]

end StructuralExhaustion.Graph.InducedPathComponentD4D7ClauseCursor
