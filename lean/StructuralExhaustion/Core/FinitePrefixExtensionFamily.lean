import StructuralExhaustion.Core.FinitePrefixExtension

namespace StructuralExhaustion.Core.FinitePrefixExtensionFamily

open FinitePrefixExtension

universe uWindow uCoord uState uFailure

/-!
# A finite family of ordered symbolic prefix passes

This module lifts `FinitePrefixExtension.Machine.run` from one application-
owned symbolic state to one explicit finite list of local objects.  Every
local object retains its own dependent machine and coordinate schedule.  The
runner returns either the first local obstruction, together with complete
ledgers for every earlier object, or complete ledgers for the whole family.

Only the supplied object list and each supplied coordinate list are scanned.
In particular, this runner does not enumerate assignments, Boolean cubes,
graphs, completions, or ambient universes, and it proves no realization or
gluing theorem.
-/

variable {Window : Type uWindow} {Coord : Type uCoord}
  (machine : Window → Machine.{uCoord, uState, uFailure} Coord)
  (coordinates : Window → List Coord)

/-- Complete symbolic ledgers for every object in the supplied order. -/
inductive AllComplete : List Window → Type (max uWindow uCoord uState uFailure) where
  | nil : AllComplete []
  | cons {window : Window} {windows : List Window}
      (head : Complete (machine window) (machine window).root
        (coordinates window))
      (tail : AllComplete windows) :
      AllComplete (window :: windows)

/-- The first object whose own coordinate pass obstructs.  Earlier objects
carry complete ledgers in the `later` constructor chain. -/
inductive FirstObstruction : List Window →
    Type (max uWindow uCoord uState uFailure) where
  | here {window : Window} {windows : List Window}
      (failure : FinitePrefixExtension.FirstObstruction
        (machine window) (machine window).root (coordinates window)) :
      FirstObstruction (window :: windows)
  | later {window : Window} {windows : List Window}
      (head : Complete (machine window) (machine window).root
        (coordinates window))
      (tail : FirstObstruction windows) :
      FirstObstruction (window :: windows)

/-- Total family-level result: first local obstruction or all local passes
complete.  Neither constructor has realization semantics by itself. -/
inductive Outcome (windows : List Window) :
    Type (max uWindow uCoord uState uFailure) where
  | firstObstruction (failure : FirstObstruction machine coordinates windows)
  | allComplete (ledgers : AllComplete machine coordinates windows)

/-- Execute the pointwise prefix runner in the supplied object order. -/
def run : (windows : List Window) → Outcome machine coordinates windows
  | [] => .allComplete .nil
  | window :: windows =>
      match (machine window).run (coordinates window) with
      | .firstObstruction failure => .firstObstruction (.here failure)
      | .complete ledger =>
          match run windows with
          | .firstObstruction failure =>
              .firstObstruction (.later ledger failure)
          | .allComplete ledgers => .allComplete (.cons ledger ledgers)

namespace FirstObstruction

/-- Zero-based position of the first obstructed object. -/
def index {windows : List Window}
    (failure : FirstObstruction machine coordinates windows) : Nat :=
  match failure with
  | .here _ => 0
  | .later _ tail => tail.index + 1

/-- The first obstruction occurs inside the supplied object list. -/
theorem index_lt {windows : List Window}
    (failure : FirstObstruction machine coordinates windows) :
    failure.index < windows.length := by
  induction failure with
  | here _ => simp [index]
  | later _ tail ih => simpa [index] using Nat.succ_lt_succ ih

end FirstObstruction

/-- The family runner has exactly its advertised exhaustive split. -/
theorem run_exhaustive (windows : List Window) :
    (∃ failure, run machine coordinates windows = .firstObstruction failure) ∨
      (∃ ledgers, run machine coordinates windows = .allComplete ledgers) := by
  cases result : run machine coordinates windows with
  | firstObstruction failure => exact Or.inl ⟨failure, rfl⟩
  | allComplete ledgers => exact Or.inr ⟨ledgers, rfl⟩

/-- The full visible-work envelope: one pointwise extension call for every
listed coordinate of every listed object.  A first obstruction may stop
strictly earlier. -/
def visibleCheckEnvelope (windows : List Window) : Nat :=
  (windows.map fun window => (coordinates window).length).sum

theorem visibleCheckEnvelope_exact (windows : List Window) :
    visibleCheckEnvelope coordinates windows =
      (windows.map fun window => (coordinates window).length).sum := rfl

end StructuralExhaustion.Core.FinitePrefixExtensionFamily
