namespace StructuralExhaustion.Core.LocalBinaryMajority

universe u

/-!
# Local binary majority on an explicit list

This module records the elementary counting step used when one already owns
an exact finite local schedule and every entry has exactly one of two tags.
The runner filters only the supplied list.  In particular, it does not search
an ambient object, state, or context universe.
-/

variable {Entry : Type u}

def leftEntries (entries : List Entry) (left : Entry → Prop)
    [DecidablePred left] : List Entry :=
  entries.filter left

def rightEntries (entries : List Entry) (left : Entry → Prop)
    [DecidablePred left] : List Entry :=
  entries.filter fun entry => ¬ left entry

/-- The two predicate filters are a lossless partition of the supplied list. -/
theorem partition_length (entries : List Entry) (left : Entry → Prop)
    [DecidablePred left] :
    (leftEntries entries left).length +
        (rightEntries entries left).length = entries.length := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
      by_cases side : left entry <;>
        simp [leftEntries, rightEntries, side] at ih ⊢ <;> omega

theorem bool_filter_partition_length (entries : List Entry)
    (left : Entry → Bool) :
    (entries.filter left).length +
      (entries.filter fun entry => !left entry).length = entries.length := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
      cases equation : left entry <;> simp [equation] <;> omega

/-- Proof-carrying outcome of the odd binary-majority decision. -/
inductive Outcome (entries : List Entry) (left : Entry → Prop)
    [DecidablePred left] (threshold : Nat) where
  | leftMajority (large : threshold ≤ (leftEntries entries left).length)
  | rightMajority (large : threshold ≤ (rightEntries entries left).length)

/-- If the local list has length `2 * radius + 1`, one of its two sides has
at least `radius + 1` entries. -/
def decideOdd (entries : List Entry) (left : Entry → Prop)
    [DecidablePred left] (radius : Nat)
    (exactLength : entries.length = 2 * radius + 1) :
    Outcome entries left (radius + 1) := by
  by_cases large : radius + 1 ≤ (leftEntries entries left).length
  · exact .leftMajority large
  · apply Outcome.rightMajority
    have partition := partition_length entries left
    omega

/-- The decision reads only the entries of the supplied local schedule. -/
def visibleChecks (entries : List Entry) : Nat := entries.length

theorem visibleChecks_exact (entries : List Entry) :
    visibleChecks entries = entries.length := rfl

end StructuralExhaustion.Core.LocalBinaryMajority
