import Mathlib.Tactic
import Hypostructure.Core.Finite.Enumeration

/-!
# Finite represented PDE schedules

Core owns finite enumerations.  This module only supplies the PDE operation
used repeatedly by CT rows: retain the scheduled windows satisfying a
decidable local predicate, preserving the inherited order and duplicate-free
certificate.
-/

namespace Hypostructure.PDE.Finite

open Hypostructure

universe u

noncomputable def filterValues
    {Window : Type u}
    (schedule : Core.Finite.Enumeration Window)
    (active : Window -> Prop)
    (activeDecidable : (window : Window) -> Decidable (active window)) : List Window :=
  schedule.values.filter
    (fun window => @decide (active window) (activeDecidable window))

noncomputable def filter
    {Window : Type u}
    (schedule : Core.Finite.Enumeration Window)
    (active : Window -> Prop)
    (activeDecidable : (window : Window) -> Decidable (active window)) :
    Core.Finite.Enumeration Window := by
  letI : DecidableEq Window := schedule.decEq
  exact Core.Finite.Enumeration.ofNodupList
    (filterValues schedule active activeDecidable)
    (schedule.nodup.filter _)

@[simp] theorem filter_values
    {Window : Type u}
    (schedule : Core.Finite.Enumeration Window)
    (active : Window -> Prop)
    (activeDecidable : (window : Window) -> Decidable (active window)) :
    (filter schedule active activeDecidable).values =
      filterValues schedule active activeDecidable :=
  rfl

theorem mem_filter_iff
    {Window : Type u}
    (schedule : Core.Finite.Enumeration Window)
    (active : Window -> Prop)
    (activeDecidable : (window : Window) -> Decidable (active window))
    (window : Window) :
    window ∈ (filter schedule active activeDecidable).values ↔
      window ∈ schedule.values ∧ active window := by
  change window ∈ filterValues schedule active activeDecidable ↔ _
  simp [filterValues]

end Hypostructure.PDE.Finite
