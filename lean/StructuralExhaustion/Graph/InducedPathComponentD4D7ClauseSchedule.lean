import StructuralExhaustion.Graph.InducedPathComponentD4D7SemanticReadiness

namespace StructuralExhaustion.Graph.InducedPathComponentD4D7ClauseSchedule

open StructuralExhaustion

universe u uMarker

/-!
# Finite D4--D7 obligation schedule

`MissingD4D7Reconstruction` is deliberately only a marker; it contains no
clause truth value, response map, context family, or removal operation.  The
first honest consumer can therefore only retain that exact marker and expose
the fixed local order in which the four missing clause slots must be supplied.
It must not decide any of those clauses.
-/

inductive ClauseSlot
  | d4
  | d5
  | d6
  | d7
  deriving DecidableEq, Repr

def clauseOrder : List ClauseSlot := [.d4, .d5, .d6, .d7]

theorem clauseOrder_nodup : clauseOrder.Nodup := by decide

@[simp] theorem clauseOrder_length : clauseOrder.length = 4 := rfl

theorem mem_clauseOrder (slot : ClauseSlot) : slot ∈ clauseOrder := by
  cases slot <;> simp [clauseOrder]

@[implicit_reducible]
def clauseSlots : FinEnum ClauseSlot :=
  FinEnum.ofList clauseOrder mem_clauseOrder

/-- One exact missing-marker occurrence and the complete fixed obligation
order.  `Marker` remains the dependent graph proposition carried by the
predecessor; it is not erased to `Unit` or a Boolean. -/
structure Ledger {Marker : Type uMarker} (source : Nonempty Marker) where
  marker : Nonempty Marker
  markerExact : marker = source
  slots : List ClauseSlot
  slotsExact : slots = clauseOrder
  slotsNodup : slots.Nodup

def ledger {Marker : Type uMarker} (source : Nonempty Marker) : Ledger source where
  marker := source
  markerExact := rfl
  slots := clauseOrder
  slotsExact := rfl
  slotsNodup := clauseOrder_nodup

@[simp] theorem ledger_slots_length {Marker : Type uMarker}
    (source : Nonempty Marker) : (ledger source).slots.length = 4 := rfl

variable {V : Type u} {object : FiniteObject V}
variable
  (input : InducedPathComponentD1D3Ledger.Input object)
  (anchorState : InducedPathComponentD1D3Ledger.State)
  (LengthOK : Nat → Prop)
  (lengthOKDecidable : DecidablePred LengthOK)

namespace Previous
export InducedPathComponentD4D7SemanticReadiness
  (CoarseBlocked BoundedBlocked Result)
end Previous

/-- Dependent output preserving the exact node-180 constructor. -/
inductive Scheduled :
    Previous.Result input anchorState LengthOK lengthOKDecidable → Type (u + 1) where
  | coarse {blocked}
      (first : Ledger blocked.firstMissing)
      (second : Ledger blocked.secondMissing) :
      Scheduled (.coarseBlocked blocked)
  | bounded {blocked}
      (only : Ledger blocked.missing) :
      Scheduled (.boundedBlocked blocked)

/-- Construct only four fixed slots per retained marker occurrence. -/
noncomputable def run
    (source : Previous.Result input anchorState LengthOK lengthOKDecidable) :
    Scheduled input anchorState LengthOK lengthOKDecidable source := by
  cases source with
  | coarseBlocked blocked =>
      exact .coarse (ledger blocked.firstMissing) (ledger blocked.secondMissing)
  | boundedBlocked blocked =>
      exact .bounded (ledger blocked.missing)

theorem run_total
    (source : Previous.Result input anchorState LengthOK lengthOKDecidable) :
    Nonempty (Scheduled input anchorState LengthOK lengthOKDecidable source) :=
  ⟨run input anchorState LengthOK lengthOKDecidable source⟩

/-- At most two actual marker occurrences, each with four fixed slots. -/
def emittedSlots
    (source : Previous.Result input anchorState LengthOK lengthOKDecidable) : Nat :=
  match source with
  | .coarseBlocked _ => 8
  | .boundedBlocked _ => 4

theorem emittedSlots_le_eight
    (source : Previous.Result input anchorState LengthOK lengthOKDecidable) :
    emittedSlots input anchorState LengthOK lengthOKDecidable source ≤ 8 := by
  cases source <;> simp [emittedSlots]

end StructuralExhaustion.Graph.InducedPathComponentD4D7ClauseSchedule
