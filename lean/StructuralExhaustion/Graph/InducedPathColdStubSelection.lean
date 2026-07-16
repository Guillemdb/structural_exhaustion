import StructuralExhaustion.Core.FiniteSearch
import StructuralExhaustion.Graph.InducedPathColdCorridor

namespace StructuralExhaustion.Graph.InducedPathColdStubSelection

open StructuralExhaustion
open InducedPathWindowLedger
open InducedPathColdLedger

universe u

variable {V : Type u}

/-!
# Canonical entry from a selected window to a cold return corridor

This layer removes the caller-supplied external stub from the cold-corridor
entry.  A non-cubic window returns its first high-degree position.  An
ambient-cubic window has exactly fifteen external incidences, so an exhaustive
scan of the existing token universe selects the first one and constructs the
literal `CubicStub` consumed by `InducedPathColdCorridor`.
-/

def BelongsToWindow {object : FiniteObject V}
    (window : WindowIndex object) (token : Token object) : Prop :=
  token.1 = window

noncomputable def belongsToWindowDecidable {object : FiniteObject V}
    (window : WindowIndex object) (token : Token object) :
    Decidable (BelongsToWindow window token) := by
  unfold BelongsToWindow
  exact @Classical.decEq (WindowIndex object) token.1 window

noncomputable def tokenSearch (object : FiniteObject V)
    (window : WindowIndex object) :=
  Core.FiniteSearch.search (tokens object) (BelongsToWindow window)
    (belongsToWindowDecidable window)

theorem exists_token_of_ambientCubic (object : FiniteObject V)
    (window : WindowIndex object) (cubic : AmbientCubic object window) :
    ∃ token : Token object, BelongsToWindow window token := by
  have count := external_stub_count_eq_fifteen object window cubic
  by_contra absent
  push Not at absent
  have empty : ∀ position : Fin 13,
      externalNeighbors object window position = ∅ := by
    intro position
    ext neighbor
    constructor
    · intro member
      exact False.elim (absent ⟨window, position, ⟨neighbor, member⟩⟩ rfl)
    · simp
  have zero : (∑ position : Fin 13,
      (externalNeighbors object window position).card) = 0 := by
    apply Finset.sum_eq_zero
    intro position _member
    rw [empty position]
    rfl
  omega

/-- External incidences of this window, in the repository's exact token
order. -/
noncomputable def matchingTokens (object : FiniteObject V)
    (window : WindowIndex object) : List (Token object) :=
  (tokens object).orderedValues.filter fun token =>
    @decide (BelongsToWindow window token)
      (belongsToWindowDecidable window token)

theorem matchingTokens_ne_nil (object : FiniteObject V)
    (window : WindowIndex object) (cubic : AmbientCubic object window) :
    matchingTokens object window ≠ [] := by
  obtain ⟨token, belongs⟩ := exists_token_of_ambientCubic object window cubic
  intro empty
  have member : token ∈ matchingTokens object window := by
    simp [matchingTokens, belongs]
  simp [empty] at member

/-- The first external incidence in the repository's exact token order. -/
noncomputable def canonicalToken (object : FiniteObject V)
    (window : WindowIndex object) (cubic : AmbientCubic object window) :
    {token : Token object // BelongsToWindow window token} := by
  refine ⟨(matchingTokens object window).head
    (matchingTokens_ne_nil object window cubic), ?_⟩
  have member := List.head_mem (matchingTokens_ne_nil object window cubic)
  simpa [matchingTokens] using member

/-- Canonical graph-owned corridor stub for one ambient-cubic window. -/
noncomputable def canonicalCubicStub (object : FiniteObject V)
    (window : WindowIndex object) (cubic : AmbientCubic object window) :
    InducedPathColdCorridor.CubicStub object := by
  let selected := canonicalToken object window cubic
  refine { token := selected.1, cubic := ?_ }
  rw [selected.2]
  exact cubic

/-- Exact both-sides entry decision for every selected window. -/
inductive Entry (object : FiniteObject V) (window : WindowIndex object) where
  | high (position : Fin 13)
      (degreeHigh : 3 < object.degree (selectedWindow object window position))
  | cubic (stub : InducedPathColdCorridor.CubicStub object)
      (sameWindow : stub.window = window)

noncomputable def nonCubicPositions (object : FiniteObject V)
    (window : WindowIndex object) : List (Fin 13) :=
  (inferInstance : FinEnum (Fin 13)).orderedValues.filter fun position =>
    decide (object.degree (selectedWindow object window position) ≠ 3)

theorem nonCubicPositions_ne_nil (object : FiniteObject V)
    (window : WindowIndex object) (notCubic : ¬AmbientCubic object window) :
    nonCubicPositions object window ≠ [] := by
  rw [AmbientCubic] at notCubic
  push Not at notCubic
  obtain ⟨position, degreeNe⟩ := notCubic
  intro empty
  have member : position ∈ nonCubicPositions object window := by
    simp [nonCubicPositions, degreeNe]
  simp [empty] at member

noncomputable def firstNonCubicPosition (object : FiniteObject V)
    (window : WindowIndex object) (notCubic : ¬AmbientCubic object window) :
    {position : Fin 13 //
      object.degree (selectedWindow object window position) ≠ 3} := by
  refine ⟨(nonCubicPositions object window).head
    (nonCubicPositions_ne_nil object window notCubic), ?_⟩
  have member := List.head_mem
    (nonCubicPositions_ne_nil object window notCubic)
  simpa [nonCubicPositions] using member

/-- Compute the first high position, or construct the canonical cubic stub.
Only the supplied minimum-degree-three theorem is used to turn degree
inequality into strict surplus. -/
noncomputable def classify (object : FiniteObject V)
    (baseline : ∀ vertex, 3 ≤ object.degree vertex)
    (window : WindowIndex object) : Entry object window := by
  by_cases cubic : AmbientCubic object window
  · let stub := canonicalCubicStub object window cubic
    exact .cubic stub (canonicalToken object window cubic).2
  · let position := firstNonCubicPosition object window cubic
    exact .high position.1 (by
      have lower := baseline (selectedWindow object window position.1)
      have degreeNe := position.2
      omega)

theorem classify_exhaustive (object : FiniteObject V)
    (baseline : ∀ vertex, 3 ≤ object.degree vertex)
    (window : WindowIndex object) :
    (∃ position high, classify object baseline window = .high position high) ∨
      (∃ stub same, classify object baseline window = .cubic stub same) := by
  cases equation : classify object baseline window with
  | high position high => exact Or.inl ⟨position, high, rfl⟩
  | cubic stub same => exact Or.inr ⟨stub, same, rfl⟩

end StructuralExhaustion.Graph.InducedPathColdStubSelection
