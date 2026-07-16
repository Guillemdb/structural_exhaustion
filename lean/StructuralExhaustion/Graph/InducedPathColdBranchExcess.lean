import StructuralExhaustion.Graph.InducedPathColdStubSelection

namespace StructuralExhaustion.Graph.InducedPathColdBranchExcess

open StructuralExhaustion
open InducedPathWindowLedger
open InducedPathColdLedger

universe u

variable {V : Type u}

/-!
# Literal branch-excess half-edges of one ambient-cubic window

The cold-skeleton argument orders all fifteen external incidences of a cubic
selected `P13`, declares the first two to be transit stubs, and retains the
remaining thirteen.  This module implements exactly that local operation.
It scans only the already existing finite incidence schedule of the supplied
window; it does not enumerate graphs, paths, contexts, or state universes.
-/

/-- One literal external incidence of one fixed selected window. -/
abbrev WindowToken (object : FiniteObject V) (window : WindowIndex object) :=
  Sigma fun position : Fin 13 =>
    {neighbor : V // neighbor ∈ externalNeighbors object window position}

/-- Exact local incidence enumeration inherited from the graph input. -/
@[implicit_reducible]
noncomputable def windowTokens (object : FiniteObject V)
    (window : WindowIndex object) : FinEnum (WindowToken object window) := by
  letI : FinEnum V := object.input.vertices
  letI : DecidableEq V := object.input.vertices.decEq
  infer_instance

/-- Its cardinality is the literal external-stub sum used in the paper. -/
theorem windowTokens_card (object : FiniteObject V)
    (window : WindowIndex object) :
    (windowTokens object window).card =
      ∑ position : Fin 13, (externalNeighbors object window position).card := by
  letI : FinEnum V := object.input.vertices
  letI : DecidableEq V := object.input.vertices.decEq
  rw [FinEnum.card_eq_fintypeCard]
  simp only [WindowToken, Fintype.card_sigma, Fintype.card_coe]

/-- An ambient-cubic window has exactly fifteen entries in that order. -/
theorem windowTokens_length_eq_fifteen (object : FiniteObject V)
    (window : WindowIndex object) (cubic : AmbientCubic object window) :
    (windowTokens object window).orderedValues.length = 15 := by
  rw [FinEnum.orderedValues_length, windowTokens_card,
    external_stub_count_eq_fifteen object window cubic]

/-- Remove exactly the first two transit stubs. -/
noncomputable def branchExcessTokens (object : FiniteObject V)
    (window : WindowIndex object) : List (WindowToken object window) :=
  (windowTokens object window).orderedValues.drop 2

/-- The paper's `15 - 2 = 13` identity as an exact list-length theorem. -/
theorem branchExcessTokens_length_eq_thirteen (object : FiniteObject V)
    (window : WindowIndex object) (cubic : AmbientCubic object window) :
    (branchExcessTokens object window).length = 13 := by
  rw [branchExcessTokens, List.length_drop,
    windowTokens_length_eq_fifteen object window cubic]

/-- The selected branch-excess schedule has no repeated incidence. -/
theorem branchExcessTokens_nodup (object : FiniteObject V)
    (window : WindowIndex object) :
    (branchExcessTokens object window).Nodup :=
  (windowTokens object window).nodup_orderedValues.drop

/-- Embed one local incidence back into the global token type without changing
its window, path position, neighbour, or membership proof. -/
def toToken {object : FiniteObject V} {window : WindowIndex object}
    (token : WindowToken object window) : Token object :=
  ⟨window, token⟩

@[simp] theorem toToken_window {object : FiniteObject V}
    {window : WindowIndex object} (token : WindowToken object window) :
    (toToken token).1 = window := rfl

theorem toToken_injective {object : FiniteObject V}
    {window : WindowIndex object} :
    Function.Injective (@toToken V object window) := by
  intro left right equal
  exact eq_of_heq (Sigma.mk.inj_iff.mp equal).2

/-- Turn every selected excess incidence into the exact cubic-stub input of
the cold-corridor producer. -/
def toCubicStub {object : FiniteObject V} {window : WindowIndex object}
    (cubic : AmbientCubic object window)
    (token : WindowToken object window) :
    InducedPathColdCorridor.CubicStub object where
  token := toToken token
  cubic := cubic

@[simp] theorem toCubicStub_window {object : FiniteObject V}
    {window : WindowIndex object} (cubic : AmbientCubic object window)
    (token : WindowToken object window) :
    (toCubicStub cubic token).window = window := rfl

noncomputable def branchExcessStubs (object : FiniteObject V)
    (window : WindowIndex object) (cubic : AmbientCubic object window) :
    List (InducedPathColdCorridor.CubicStub object) :=
  (branchExcessTokens object window).map (toCubicStub cubic)

theorem branchExcessStubs_length_eq_thirteen (object : FiniteObject V)
    (window : WindowIndex object) (cubic : AmbientCubic object window) :
    (branchExcessStubs object window cubic).length = 13 := by
  rw [branchExcessStubs, List.length_map,
    branchExcessTokens_length_eq_thirteen object window cubic]

theorem branchExcessStubs_same_window (object : FiniteObject V)
    (window : WindowIndex object) (cubic : AmbientCubic object window)
    (stub : InducedPathColdCorridor.CubicStub object)
    (member : stub ∈ branchExcessStubs object window cubic) :
    stub.window = window := by
  rw [branchExcessStubs, List.mem_map] at member
  obtain ⟨token, _tokenMem, rfl⟩ := member
  rfl

theorem branchExcessStubs_nodup (object : FiniteObject V)
    (window : WindowIndex object) (cubic : AmbientCubic object window) :
    (branchExcessStubs object window cubic).Nodup := by
  apply (branchExcessTokens_nodup object window).map
  intro left right equal
  exact toToken_injective (congrArg InducedPathColdCorridor.CubicStub.token equal)

end StructuralExhaustion.Graph.InducedPathColdBranchExcess
