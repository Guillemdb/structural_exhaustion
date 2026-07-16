import StructuralExhaustion.Graph.InducedPathWindowLedger
import Mathlib.Tactic

namespace StructuralExhaustion.Graph.InducedPathColdLedger

open StructuralExhaustion
open InducedPathWindowLedger

universe u

variable {V : Type u}

/-!
# Ambient-cubic filtering and exact cold-window arithmetic

This module works on an explicitly supplied finite subfamily of the already
selected induced-`P13` packing.  It computes the ambient-cubic filter and
proves the exact `39 - 24 = 15` stub and `15 - 2 = 13` branch-excess
identities for every retained window.
-/

noncomputable def AmbientCubic (object : FiniteObject V)
    (window : WindowIndex object) : Prop :=
  ∀ position : Fin 13,
    object.degree (selectedWindow object window position) = 3

noncomputable def ambientCubicDecidable (object : FiniteObject V)
    (window : WindowIndex object) : Decidable (AmbientCubic object window) := by
  unfold AmbientCubic
  infer_instance

noncomputable def ambientCubicWindows (object : FiniteObject V)
    (cold : Finset (WindowIndex object)) : Finset (WindowIndex object) := by
  letI : DecidablePred (AmbientCubic object) := ambientCubicDecidable object
  exact cold.filter (AmbientCubic object)

noncomputable def nonAmbientCubicWindows (object : FiniteObject V)
    (cold : Finset (WindowIndex object)) : Finset (WindowIndex object) := by
  letI : DecidablePred (AmbientCubic object) := ambientCubicDecidable object
  exact cold.filter fun window ↦ ¬AmbientCubic object window

/-- Node `[151]`: exact, lossless partition of the supplied cold family. -/
theorem ambientCubic_card_add_nonAmbientCubic_card
    (object : FiniteObject V) (cold : Finset (WindowIndex object)) :
    (ambientCubicWindows object cold).card +
      (nonAmbientCubicWindows object cold).card = cold.card := by
  letI : DecidablePred (AmbientCubic object) := ambientCubicDecidable object
  simpa [ambientCubicWindows, nonAmbientCubicWindows] using
    (Finset.card_filter_add_card_filter_not
      (s := cold) (p := AmbientCubic object))

/-- Quantitative filtering form: if at most `loss` cold windows are
non-cubic, the retained ambient-cubic family loses at most `loss`. -/
theorem cold_card_le_ambientCubic_add_loss
    (object : FiniteObject V) (cold : Finset (WindowIndex object))
    (loss : Nat)
    (nonCubicBound : (nonAmbientCubicWindows object cold).card ≤ loss) :
    cold.card ≤ (ambientCubicWindows object cold).card + loss := by
  rw [← ambientCubic_card_add_nonAmbientCubic_card object cold]
  omega

set_option maxHeartbeats 800000 in
/-- Node `[151]`, graph-grounded form: under the inherited minimum-degree
three baseline, every non-ambient-cubic selected window contains a position
of degree at least four.  Pairwise disjointness of the selected packing means
the existing position-indexed `windowSurplus` ledger pays one distinct unit
for each such window. -/
theorem nonAmbientCubic_card_le_windowSurplus
    (object : FiniteObject V) (cold : Finset (WindowIndex object))
    (baseline : ∀ vertex, 3 ≤ object.degree vertex) :
    (nonAmbientCubicWindows object cold).card ≤ windowSurplus object := by
  classical
  letI : DecidablePred (AmbientCubic object) := ambientCubicDecidable object
  let localSurplus := fun window : WindowIndex object ↦
    ∑ position : Fin 13,
      (object.degree (selectedWindow object window position) - 3)
  have eachPays : ∀ window ∈ nonAmbientCubicWindows object cold,
      1 ≤ localSurplus window := by
    intro window member
    have notCubic : ¬AmbientCubic object window := by
      rw [nonAmbientCubicWindows, Finset.mem_filter] at member
      exact member.2
    rw [AmbientCubic] at notCubic
    push Not at notCubic
    rcases notCubic with ⟨position, degreeNe⟩
    have degreeAtLeast := baseline (selectedWindow object window position)
    have unitAtPosition :
        1 ≤ object.degree (selectedWindow object window position) - 3 := by
      omega
    exact unitAtPosition.trans (Finset.single_le_sum
      (s := Finset.univ)
      (f := fun candidate : Fin 13 ↦
        object.degree (selectedWindow object window candidate) - 3)
      (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ position))
  calc
    (nonAmbientCubicWindows object cold).card =
        ∑ _window ∈ nonAmbientCubicWindows object cold, 1 := by simp
    _ ≤ ∑ window ∈ nonAmbientCubicWindows object cold,
        localSurplus window :=
      Finset.sum_le_sum eachPays
    _ ≤ ∑ window : WindowIndex object, localSurplus window :=
      Finset.sum_le_univ_sum_of_nonneg (fun _ ↦ Nat.zero_le _)
    _ = windowSurplus object := rfl

/-- Consequently the ambient-cubic cold family loses at most the already
computed window-surplus ledger; no external non-cubic bound is requested. -/
theorem cold_card_le_ambientCubic_add_windowSurplus
    (object : FiniteObject V) (cold : Finset (WindowIndex object))
    (baseline : ∀ vertex, 3 ≤ object.degree vertex) :
    cold.card ≤
      (ambientCubicWindows object cold).card + windowSurplus object :=
  cold_card_le_ambientCubic_add_loss object cold (windowSurplus object)
    (nonAmbientCubic_card_le_windowSurplus object cold baseline)

/-- Public near-cubic form, paid by the inherited total surplus. -/
theorem nonAmbientCubic_card_le_totalSurplus
    (object : FiniteObject V) (cold : Finset (WindowIndex object))
    (baseline : ∀ vertex, 3 ≤ object.degree vertex) :
    (nonAmbientCubicWindows object cold).card ≤ totalSurplus object := by
  calc
    (nonAmbientCubicWindows object cold).card ≤ windowSurplus object :=
      nonAmbientCubic_card_le_windowSurplus object cold baseline
    _ = coveredSurplus object := windowSurplus_eq_coveredSurplus object
    _ ≤ totalSurplus object := by
      have partition := covered_add_remainder_eq_totalSurplus object
      omega

/-- The two numerical identities used by node `[152]`. -/
theorem p13_cubic_degree_sum : 13 * 3 = 39 := by decide

theorem p13_internal_degree_sum : 2 * 12 = 24 := by decide

theorem p13_external_stub_arithmetic : 13 * 3 - 2 * 12 = 15 := by decide

theorem p13_branch_excess_arithmetic : (13 * 3 - 2 * 12) - 2 = 13 := by
  decide

/-- One ambient-cubic selected induced `P13` has exactly fifteen literal
external edge ends in the existing window-incidence universe. -/
theorem external_stub_count_eq_fifteen
    (object : FiniteObject V) (window : WindowIndex object)
    (cubic : AmbientCubic object window) :
    (∑ position : Fin 13,
      (externalNeighbors object window position).card) = 15 := by
  have degreeSum :
      (∑ position : Fin 13,
        object.degree (selectedWindow object window position)) = 39 := by
    calc
      (∑ position : Fin 13,
          object.degree (selectedWindow object window position)) =
          ∑ _position : Fin 13, 3 := by
            apply Finset.sum_congr rfl
            intro position _
            exact cubic position
      _ = 39 := by decide
  have split := one_window_degree_sum object window
  omega

/-- After the two canonical transit stubs are removed, exactly thirteen
selected branch-excess half-edges remain. -/
theorem branchExcess_eq_thirteen
    (object : FiniteObject V) (window : WindowIndex object)
    (cubic : AmbientCubic object window) :
    (∑ position : Fin 13,
      (externalNeighbors object window position).card) - 2 = 13 := by
  rw [external_stub_count_eq_fifteen object window cubic]

end StructuralExhaustion.Graph.InducedPathColdLedger
