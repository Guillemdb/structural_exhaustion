import Hypostructure.CT3.Automation
import Hypostructure.CT3.Schedule

/-!
# Scheduled CT3 execution

This module owns the generic bridge from a residual-owned finite family of
bounded entries to the CT3 terminal schedule used by downstream CT3 schedule
classification.  Domains provide only the already-registered CT3 spec,
capability, exact item schedule, and item-to-input query.  CT3 runs the
existing executor for each item and exposes only the derived terminal map.
-/

namespace Hypostructure.CT3.RunSchedule

open Hypostructure.Core
open Hypostructure.Core.Residual

universe uPrevious uCTPrevious uRepresentative uContext uCoordinate uValue
universe uCandidate uRow uItem

/-- Build a CT3 terminal schedule by executing the same registered CT3
capability on every item selected by the active residual. -/
noncomputable def focused {Previous : Sort uPrevious}
    {focus : Focus.Profile Previous}
    {CTPrevious : Type uCTPrevious}
    (spec : Spec.{uCTPrevious, uRepresentative, uContext, uCoordinate, uValue,
      uCandidate, uRow} CTPrevious)
    (capability : Capability spec)
    (Item : Type uItem)
    (items :
      Focus.ActiveQuery focus fun _previous _active =>
        Finite.Enumeration Item)
    (input :
      Focus.ActiveQuery focus fun _previous _active =>
        Item -> CTPrevious) :
    Schedule.FocusedContract focus where
  Item := Item
  items := items
  terminal := fun previous active item =>
    (execute spec capability ((input.read previous active) item)).terminal

/-- Query the exact CT3 execution result for one scheduled item.  This keeps
the per-item CT3 run behind the same residual-query surface as the derived
terminal schedule. -/
noncomputable def resultAt {Previous : Sort uPrevious}
    {focus : Focus.Profile Previous}
    {CTPrevious : Type uCTPrevious}
    (spec : Spec.{uCTPrevious, uRepresentative, uContext, uCoordinate, uValue,
      uCandidate, uRow} CTPrevious)
    (capability : Capability spec)
    (Item : Type uItem)
    (input :
      Focus.ActiveQuery focus fun _previous _active =>
        Item -> CTPrevious) :
    Focus.ActiveQuery focus fun _previous _active =>
      Item -> ExecutionResult spec capability :=
  Focus.ActiveQuery.ofFunction fun previous active item =>
    execute spec capability ((input.read previous active) item)

/-- The terminal schedule reads exactly the terminal of the per-item CT3
execution result. -/
theorem focused_terminal_eq_resultAt {Previous : Sort uPrevious}
    {focus : Focus.Profile Previous}
    {CTPrevious : Type uCTPrevious}
    (spec : Spec.{uCTPrevious, uRepresentative, uContext, uCoordinate, uValue,
      uCandidate, uRow} CTPrevious)
    (capability : Capability spec)
    (Item : Type uItem)
    (items :
      Focus.ActiveQuery focus fun _previous _active =>
        Finite.Enumeration Item)
    (input :
      Focus.ActiveQuery focus fun _previous _active =>
        Item -> CTPrevious)
    (previous : Previous) (active : focus.Active previous)
    (item : Item) :
    (focused spec capability Item items input).terminal previous active item =
      ((resultAt spec capability Item input).read previous active item).terminal :=
  rfl

/-- Execute the scheduled CT3 terminal classifier directly.  This is the
framework-owned composition of per-item CT3 execution with the schedule
all-good/first-residual split; applications should not manually thread the
intermediate focused contract when they just need the classified stage. -/
noncomputable def runClassified {Previous : Sort uPrevious}
    {focus : Focus.Profile Previous}
    {CTPrevious : Type uCTPrevious}
    (spec : Spec.{uCTPrevious, uRepresentative, uContext, uCoordinate, uValue,
      uCandidate, uRow} CTPrevious)
    (capability : Capability spec)
    (Item : Type uItem)
    (items :
      Focus.ActiveQuery focus fun _previous _active =>
        Finite.Enumeration Item)
    (input :
      Focus.ActiveQuery focus fun _previous _active =>
        Item -> CTPrevious)
    (previous : Previous) :
    (focused spec capability Item items input).Stage :=
  (focused spec capability Item items input).runStage previous

@[simp] theorem runClassified_previous {Previous : Sort uPrevious}
    {focus : Focus.Profile Previous}
    {CTPrevious : Type uCTPrevious}
    (spec : Spec.{uCTPrevious, uRepresentative, uContext, uCoordinate, uValue,
      uCandidate, uRow} CTPrevious)
    (capability : Capability spec)
    (Item : Type uItem)
    (items :
      Focus.ActiveQuery focus fun _previous _active =>
        Finite.Enumeration Item)
    (input :
      Focus.ActiveQuery focus fun _previous _active =>
        Item -> CTPrevious)
    (previous : Previous) :
    (runClassified spec capability Item items input previous).previous =
      previous :=
  (focused spec capability Item items input).runStage_previous previous

end Hypostructure.CT3.RunSchedule
