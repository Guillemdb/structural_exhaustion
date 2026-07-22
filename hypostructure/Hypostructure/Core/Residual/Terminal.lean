import Hypostructure.Core.Residual.Focus

/-!
# Focused proof-only terminals

This is the zero-local-work focused continuation used when a branch is closed
or marked terminal by a previously registered certificate.  Core preserves the
literal predecessor and owns the single focused extension; applications supply
no successor object, route, or copied payload.
-/

namespace Hypostructure.Core.Residual.Terminal

open Hypostructure.Core
open Hypostructure.Core.Residual

universe uPrevious

/-- Framework-owned terminal marker. -/
inductive Marker where
  | closed : Marker

/-- One proof-only focused terminal extension. -/
abbrev Stage {Previous : Sort uPrevious} (focus : Focus.Profile Previous) :=
  Focus.Stage focus fun _previous _active => Marker

/-- The successor focus of a proof-only terminal branch. -/
abbrev successor {Previous : Sort uPrevious} (focus : Focus.Profile Previous) :
    Focus.Profile (Stage focus) :=
  Focus.successor focus fun _previous _active => Marker

/-- Execute a terminal marker on the active branch.  The only work is the
inherited focus selector. -/
def executeCounted {Previous : Sort uPrevious}
    (focus : Focus.Profile Previous) (previous : Previous) :
    Counted (Stage focus) :=
  Focus.runCounted focus previous fun _active _checks _exact => Marker.closed

/-- Uncounted terminal stage. -/
def execute {Previous : Sort uPrevious}
    (focus : Focus.Profile Previous) (previous : Previous) : Stage focus :=
  (executeCounted focus previous).value

@[simp] theorem execute_previous {Previous : Sort uPrevious}
    (focus : Focus.Profile Previous) (previous : Previous) :
    (execute focus previous).previous = previous :=
  Focus.runCounted_previous focus previous _

/-- Exact selector-only work. -/
theorem executeCounted_checks {Previous : Sort uPrevious}
    (focus : Focus.Profile Previous) (previous : Previous) :
    (executeCounted focus previous).checks =
      focus.selectionBudget.checks previous :=
  Focus.runCounted_checks focus previous _

/-- Predicate-form work theorem, avoiding downstream budget unfolding. -/
theorem executeCounted_work_within {Previous : Sort uPrevious}
    (focus : Focus.Profile Previous) (previous : Previous) :
    focus.selectionBudget.Within previous
      (executeCounted focus previous).checks := by
  rw [executeCounted_checks]
  exact focus.selectionBudget.checks_within previous

/-- Read the terminal marker introduced by the latest focused extension. -/
def latest {Previous : Sort uPrevious} (focus : Focus.Profile Previous) :
    Focus.ActiveQuery (successor focus) fun _stage _active => Marker :=
  Focus.ActiveQuery.latest

end Hypostructure.Core.Residual.Terminal
