import Erdos64EG.CT10P13MultiScaleCurvature
import StructuralExhaustion.Graph.LocalBooleanWindowLedger
import Mathlib.Tactic

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u uCoordinate uState

/-!
# Classifier support for a local hot/cold `P₁₃` interface

This is reusable support for the formal repair boundary behind manuscript
nodes `[145]`, `[148]`, and `[150]`; it is not by itself an implementation of
those nodes.  It deliberately does not accept a Boolean realization premise
and does not claim a global product of window systems.  The only author data
are the finite local coordinate/state universes and their response evaluator.
The framework exhaustively classifies each already selected CT12 window:

* hot carries a genuine local complete-realization constructor and hence the
  existing unconditional Boolean entropy bound;
* cold carries the first locally missing Boolean assignment.

Any later density argument may count these two lists, but it cannot use a cold
entry as though realization had merely been left to the caller.

The remaining application-owned constructor is intentionally visible as
`P13LocalBooleanData.system`: from the exact node-`[21]` prefix and one actual
selected window, it must build the finite admissible attachment-state universe
and its response evaluator.  Node `[21]` currently supplies compatibility
rows and safe/flat barrier counts, not that graph-owned state universe.
-/

/-- One member of the exact CT12-selected maximum packing. -/
abbrev SelectedP13Window
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  {window : InducedP13Window ctx // window ∈ p13Windows ctx}

@[implicit_reducible]
noncomputable def selectedP13Windows
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    FinEnum (SelectedP13Window ctx) :=
  @FinEnum.ofNodupList (SelectedP13Window ctx) (Classical.decEq _)
    (p13Windows ctx).attach
    (by rintro ⟨window, member⟩; simp)
    (by
      exact (inducedP13PackingProfile ctx).values_nodup.attach)

theorem selectedP13Windows_card
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    (selectedP13Windows ctx).card = p13 ctx := by
  simp [p13, FinEnum.card]
  rfl

/-- Raw local response data.  There is intentionally no `realizes`, `hot`,
entropy, or density field. -/
structure P13LocalBooleanData
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedP13MultiScaleCurvaturePrefix ctx) where
  system : SelectedP13Window ctx →
    Core.LocalBooleanRealization.System.{uCoordinate, uState}

namespace P13LocalBooleanData

variable {ctx : Core.MinimalCounterexampleContext
  PackedProblem.{u} PackedTarget.{u}}
variable {previous : VerifiedP13MultiScaleCurvaturePrefix ctx}

/-- Classifier support for node `[145]`: run the reusable family classifier on
exactly the windows selected by the earlier CT12 stage, indexed by the exact
node-`[21]` prefix. -/
noncomputable def family
    (data : P13LocalBooleanData.{u, uCoordinate, uState} ctx previous) :
    Graph.LocalBooleanWindowLedger.Family where
  Window := SelectedP13Window ctx
  windows := selectedP13Windows ctx
  system := data.system

abbrev HotWindow
    (data : P13LocalBooleanData.{u, uCoordinate, uState} ctx previous) :=
  data.family.HotWindow

abbrev ColdWindow
    (data : P13LocalBooleanData.{u, uCoordinate, uState} ctx previous) :=
  data.family.ColdWindow

noncomputable def hotWindows
    (data : P13LocalBooleanData.{u, uCoordinate, uState} ctx previous) :
    List data.HotWindow :=
  data.family.hotWindows

noncomputable def coldWindows
    (data : P13LocalBooleanData.{u, uCoordinate, uState} ctx previous) :
    List data.ColdWindow :=
  data.family.coldWindows

/-- Exact local hot/cold partition of the predecessor's packed windows. -/
theorem hotCount_add_coldCount
    (data : P13LocalBooleanData.{u, uCoordinate, uState} ctx previous) :
    data.hotWindows.length + data.coldWindows.length = p13 ctx := by
  rw [hotWindows, coldWindows, data.family.hotCount_add_coldCount,
    family, selectedP13Windows_card]

/-- Intended node-`[148]` consumer, local and unconditional once the missing
graph-owned raw-system constructor is supplied: a hot entry carries precisely
the complete-realization certificate consumed by the Core entropy theorem. -/
theorem hotWindow_entropyBound
    (data : P13LocalBooleanData.{u, uCoordinate, uState} ctx previous)
    (hot : data.HotWindow) :
    2 ^ (data.system hot.window).coordinates.card ≤
      (data.system hot.window).states.card :=
  hot.entropyBound

/-- Intended node-`[150]` payload: every classifier-produced cold entry
exposes an actual missing local assignment. -/
theorem coldWindow_missingAssignment
    (data : P13LocalBooleanData.{u, uCoordinate, uState} ctx previous)
    (cold : data.ColdWindow) :
    ∀ state, (data.system cold.window).value state ≠
      cold.residual.assignment :=
  cold.residual.noState

/-- Pure counting handoff used after a later theorem bounds the hot count.
No density or entropy closure is smuggled into this interface. -/
theorem coldCount_ge_sub_of_hotCount_le
    (data : P13LocalBooleanData.{u, uCoordinate, uState} ctx previous)
    (hotCeiling : Nat)
    (hotBound : data.hotWindows.length ≤ hotCeiling) :
    p13 ctx - hotCeiling ≤ data.coldWindows.length := by
  have partition := data.hotCount_add_coldCount
  omega

/-- The complete finite check budget exposed to downstream audit code. -/
noncomputable def checkBudget
    (data : P13LocalBooleanData.{u, uCoordinate, uState} ctx previous) : Nat :=
  data.family.totalCheckBudget

end P13LocalBooleanData

/-- Predecessor-indexed classifier support.  It stores the exact node-`[21]`
prefix and raw local data; it does not certify that the graph-owned raw-system
constructor has been implemented canonically. -/
structure P13HotColdClassifierSupport
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedP13MultiScaleCurvaturePrefix ctx) where
  predecessor : VerifiedP13MultiScaleCurvaturePrefix ctx
  data : P13LocalBooleanData.{u, uCoordinate, uState} ctx previous

noncomputable def p13HotColdClassifierSupport
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedP13MultiScaleCurvaturePrefix ctx)
    (data : P13LocalBooleanData.{u, uCoordinate, uState} ctx previous) :
    P13HotColdClassifierSupport.{u, uCoordinate, uState} ctx previous where
  predecessor := previous
  data := data

end Erdos64EG.Internal
