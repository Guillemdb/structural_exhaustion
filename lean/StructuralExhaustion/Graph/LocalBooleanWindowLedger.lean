import StructuralExhaustion.Core.LocalBooleanRealization
import Mathlib.Tactic

namespace StructuralExhaustion.Graph.LocalBooleanWindowLedger

open StructuralExhaustion

universe uWindow uCoordinate uState

/-!
# Finite hot/cold ledger for local response systems

This family layer classifies each explicitly supplied local window with the
Core exhaustive realization runner.  A hot entry owns a complete Boolean
realization certificate.  A cold entry owns a missing assignment.  The list
partition is exhaustive and does not ask the caller to label either branch.
-/

/-- A finite family of bounded local response systems. -/
structure Family where
  Window : Type uWindow
  windows : FinEnum Window
  system : Window → Core.LocalBooleanRealization.System.{uCoordinate, uState}

namespace Family

variable (family : Family)

/-- A hot window can only be constructed by retaining the positive output of
the local exhaustive classifier. -/
structure HotWindow where
  window : family.Window
  certificate : (family.system window).HotCertificate

/-- A cold window carries the explicit missing local Boolean vector selected
by the same exhaustive classifier. -/
structure ColdWindow where
  window : family.Window
  residual : (family.system window).ColdResidual

/-- The classifier output for one window, with no caller-authored tag. -/
def classifyWindow (window : family.Window) :
    family.HotWindow ⊕ family.ColdWindow :=
  match (family.system window).classify with
  | .hot certificate => Sum.inl ⟨window, certificate⟩
  | .cold residual => Sum.inr ⟨window, residual⟩

private def hotOfList (family : Family) :
    List family.Window → List family.HotWindow
  | [] => []
  | window :: tail =>
      match family.classifyWindow window with
      | .inl hot => hot :: hotOfList family tail
      | .inr _ => hotOfList family tail

private def coldOfList (family : Family) :
    List family.Window → List family.ColdWindow
  | [] => []
  | window :: tail =>
      match family.classifyWindow window with
      | .inl _ => coldOfList family tail
      | .inr cold => cold :: coldOfList family tail

/-- Deterministic hot list in the original window order. -/
def hotWindows : List family.HotWindow :=
  hotOfList family family.windows.orderedValues

/-- Deterministic cold list in the original window order. -/
def coldWindows : List family.ColdWindow :=
  coldOfList family family.windows.orderedValues

private theorem hot_cold_length (values : List family.Window) :
    (hotOfList family values).length + (coldOfList family values).length =
      values.length := by
  induction values with
  | nil => rfl
  | cons window tail ih =>
      simp only [hotOfList, coldOfList]
      cases family.classifyWindow window <;>
        simp only [List.length_cons]
      all_goals omega

/-- Exact hot/cold partition count.  Every supplied window contributes once,
and no third or untyped residual exists. -/
theorem hotCount_add_coldCount :
    family.hotWindows.length + family.coldWindows.length = family.windows.card := by
  simpa [hotWindows, coldWindows] using
    family.hot_cold_length family.windows.orderedValues

/-- The pre-partition search budget: for each window, at most one scan of all
explicit assignments against all explicit local states. -/
def localCheckBudget (window : family.Window) : Nat :=
  2 ^ (family.system window).coordinates.card *
    (family.system window).states.card

def totalCheckBudget : Nat :=
  (family.windows.orderedValues.map family.localCheckBudget).sum

/-- Every retained hot entry feeds the existing unconditional entropy
theorem. -/
theorem HotWindow.entropyBound (hot : family.HotWindow) :
    2 ^ (family.system hot.window).coordinates.card ≤
      (family.system hot.window).states.card :=
  hot.certificate.two_pow_coordinateCard_le_stateCard

/-- Every retained cold entry is a genuine failure of complete realization,
not a missing premise. -/
theorem ColdWindow.notComplete (cold : family.ColdWindow) :
    ¬(∀ assignment : (family.system cold.window).Assignment,
      ∃ state, (family.system cold.window).value state = assignment) :=
  cold.residual.not_complete

end Family

/-! ## Transfer fixture

Two tiny local systems exercise both sides independently of any graph problem.
The first realizes its one-coordinate cube; the second has two coordinates
but forces the second response to `false`, so its `true,true` vector is cold.
-/

namespace Fixture

def hotSystem : Core.LocalBooleanRealization.System where
  Coordinate := Unit
  State := Bool
  coordinates := Core.Enumeration.unit
  states := Core.Enumeration.bool
  value := fun state _coordinate ↦ state

def coldSystem : Core.LocalBooleanRealization.System where
  Coordinate := Bool
  State := Bool
  coordinates := Core.Enumeration.bool
  states := Core.Enumeration.bool
  value := fun state coordinate ↦ if coordinate then false else state

def family : Family where
  Window := Bool
  windows := Core.Enumeration.bool
  system := fun window ↦ if window then coldSystem else hotSystem

theorem one_hot_one_cold :
    family.hotWindows.length = 1 ∧ family.coldWindows.length = 1 := by
  native_decide

theorem partition_is_exact :
    family.hotWindows.length + family.coldWindows.length = 2 := by
  native_decide

end Fixture

end StructuralExhaustion.Graph.LocalBooleanWindowLedger
