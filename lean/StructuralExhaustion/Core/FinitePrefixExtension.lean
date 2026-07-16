namespace StructuralExhaustion.Core.FinitePrefixExtension

universe uCoord uState uFailure

/-!
# Ordered symbolic prefix extension

This profile scans one explicit coordinate schedule.  Its application-owned
state represents all prefixes admitted so far; it is not a list of Boolean
assignments.  At each coordinate the application returns either one symbolic
state for the extended prefix family or a graph-derived obstruction.  The
framework records the first obstruction and its exact clean coordinate prefix.

Consequently the runner performs exactly one step per visited coordinate.  It
never enumerates a Boolean cube and never accepts a caller-selected bit.
-/

/-- One application-owned symbolic extension step. -/
inductive Step (State : Nat → Type uState) (Failure : Nat → Type uFailure)
    (k : Nat) where
  | extended (next : State (k + 1))
  | obstructed (failure : Failure k)

/-- A symbolic prefix-extension machine over one explicit coordinate order. -/
structure Machine (Coord : Type uCoord) where
  State : Nat → Type uState
  Failure : Nat → Type uFailure
  root : State 0
  extend : {k : Nat} → State k → Coord → Step State Failure k

variable {Coord : Type uCoord}
  (machine : Machine.{uCoord, uState, uFailure} Coord)

/-- Proof that the complete coordinate schedule extended symbolically. -/
inductive Complete : {k : Nat} → machine.State k → List Coord →
    Type (max uCoord uState uFailure) where
  | nil (state : machine.State k) : Complete state []
  | cons {state : machine.State k} {coordinate : Coord} {coordinates : List Coord}
      (next : machine.State (k + 1))
      (stepExact : machine.extend state coordinate = .extended next)
      (tail : Complete next coordinates) :
      Complete state (coordinate :: coordinates)

/-- The first graph-derived obstruction, with every earlier symbolic extension
retained in the constructor chain. -/
inductive FirstObstruction : {k : Nat} → machine.State k → List Coord →
    Type (max uCoord uState uFailure) where
  | here {state : machine.State k} {coordinate : Coord} {coordinates : List Coord}
      (failure : machine.Failure k)
      (stepExact : machine.extend state coordinate = .obstructed failure) :
      FirstObstruction state (coordinate :: coordinates)
  | later {state : machine.State k} {coordinate : Coord} {coordinates : List Coord}
      (next : machine.State (k + 1))
      (stepExact : machine.extend state coordinate = .extended next)
      (tail : FirstObstruction next coordinates) :
      FirstObstruction state (coordinate :: coordinates)

/-- Exhaustive output of one ordered symbolic pass. -/
inductive Outcome (state : machine.State k) (coordinates : List Coord) :
    Type (max uCoord uState uFailure) where
  | firstObstruction (failure : FirstObstruction machine state coordinates)
  | complete (ledger : Complete machine state coordinates)

/-- Reference interpreter.  Only the explicit coordinate list is traversed. -/
def runFrom : {k : Nat} → (state : machine.State k) →
    (coordinates : List Coord) → Outcome machine state coordinates
  | _, state, [] => .complete (.nil state)
  | _, state, coordinate :: coordinates =>
      match stepExact : machine.extend state coordinate with
      | .obstructed failure =>
          .firstObstruction (.here failure stepExact)
      | .extended next =>
          match runFrom next coordinates with
          | .firstObstruction failure =>
              .firstObstruction (.later next stepExact failure)
          | .complete ledger =>
              .complete (.cons next stepExact ledger)

/-- Execute from the application-owned symbolic root. -/
def Machine.run (coordinates : List Coord) :
    Outcome machine machine.root coordinates :=
  runFrom machine machine.root coordinates

namespace FirstObstruction

/-- Zero-based position of the first obstruction. -/
def index {state : machine.State k} {coordinates : List Coord}
    (failure : FirstObstruction machine state coordinates) : Nat :=
  match failure with
  | .here _ _ => 0
  | .later _ _ tail => tail.index + 1

/-- The obstructed coordinate. -/
def coordinate {state : machine.State k} {coordinates : List Coord}
    (failure : FirstObstruction machine state coordinates) : Coord :=
  match failure with
  | .here (coordinate := coordinate) _ _ => coordinate
  | .later _ _ tail => tail.coordinate

/-- The graph-derived obstruction payload. -/
noncomputable def payload {state : machine.State k} {coordinates : List Coord}
    (failure : FirstObstruction machine state coordinates) :
    machine.Failure (k + failure.index) := by
  induction failure with
  | here payload _ => simpa [index] using payload
  | later _ _ tail ih => simpa [index, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih

/-- The first obstruction is always one of the supplied coordinates. -/
theorem index_lt {state : machine.State k} {coordinates : List Coord}
    (failure : FirstObstruction machine state coordinates) :
    failure.index < coordinates.length := by
  induction failure with
  | here _ _ => simp [index]
  | later _ _ tail ih => simpa [index] using Nat.succ_lt_succ ih

end FirstObstruction

/-- The runner has exactly the advertised complete/first-obstruction split. -/
theorem runFrom_exhaustive {k : Nat} (state : machine.State k)
    (coordinates : List Coord) :
    (∃ failure, runFrom machine state coordinates = .firstObstruction failure) ∨
      (∃ ledger, runFrom machine state coordinates = .complete ledger) := by
  cases result : runFrom machine state coordinates with
  | firstObstruction failure => exact Or.inl ⟨failure, rfl⟩
  | complete ledger => exact Or.inr ⟨ledger, rfl⟩

/-- Visible work is one symbolic extension call per visited coordinate. -/
def visibleChecks (coordinates : List Coord) : Nat := coordinates.length

theorem visibleChecks_linear (coordinates : List Coord) :
    visibleChecks coordinates ≤ coordinates.length := Nat.le_refl _

end StructuralExhaustion.Core.FinitePrefixExtension
