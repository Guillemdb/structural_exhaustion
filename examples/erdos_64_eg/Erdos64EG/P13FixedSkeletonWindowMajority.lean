import Erdos64EG.P13FixedSkeletonComponentEntries
import StructuralExhaustion.Core.LocalBinaryMajority

namespace Erdos64EG.Internal

open StructuralExhaustion
open StructuralExhaustion.Graph
open StructuralExhaustion.Core.LocalBinaryMajority

universe u

/-!
# Per-window component/cross-window majority

For one already selected ambient-cubic `P₁₃` window, this stage recomputes
the exact thirteen branch-excess sources from the predecessor and applies the
component-entry route to each of them.  It then makes the paper's local odd
majority split: at least seven entries enter outside components, or at least
seven are literal cross-window incidences.

Only these thirteen actual entries are inspected.  No graph, component,
window-family, state, response, or context universe is enumerated.
-/

/-- The exact component-entry decision for each of one window's thirteen
branch-excess sources. -/
noncomputable def p13WindowBranchExcessComponentEntries
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (window : P13AmbientCubicWindow ctx) :
    List (P13BranchExcessComponentEntry ctx) :=
  (p13WindowBranchExcessCorridors ctx window).map fun source =>
    { source := ⟨window, source⟩
      route := InducedPathBranchExcessComponentEntry.route
        (p13SelectedWindowCorridorProducer ctx) source.stub
      routeExact := rfl }

theorem p13WindowBranchExcessComponentEntries_length
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (window : P13AmbientCubicWindow ctx) :
    (p13WindowBranchExcessComponentEntries ctx window).length = 13 := by
  rw [p13WindowBranchExcessComponentEntries, List.length_map,
    p13WindowBranchExcessCorridors_length]

/-- Every entry in the local schedule retains the supplied window as its
literal predecessor owner. -/
theorem p13WindowBranchExcessComponentEntry_sourceWindow
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {window : P13AmbientCubicWindow ctx}
    {entry : P13BranchExcessComponentEntry ctx}
    (member : entry ∈ p13WindowBranchExcessComponentEntries ctx window) :
    entry.source.1 = window := by
  rw [p13WindowBranchExcessComponentEntries] at member
  rcases List.mem_map.mp member with ⟨source, _sourceMember, rfl⟩
  rfl

noncomputable def p13WindowComponentEntries
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (window : P13AmbientCubicWindow ctx) :
    List (P13BranchExcessComponentEntry ctx) :=
  leftEntries (p13WindowBranchExcessComponentEntries ctx window)
    fun entry => entry.tag = .component

noncomputable def p13WindowCrossWindowEntries
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (window : P13AmbientCubicWindow ctx) :
    List (P13BranchExcessComponentEntry ctx) :=
  rightEntries (p13WindowBranchExcessComponentEntries ctx window)
    fun entry => entry.tag = .component

/-- The complementary local filter consists exactly of cross-window
constructors, rather than an untyped catch-all branch. -/
theorem mem_p13WindowCrossWindowEntries_iff
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {window : P13AmbientCubicWindow ctx}
    {entry : P13BranchExcessComponentEntry ctx} :
    entry ∈ p13WindowCrossWindowEntries ctx window ↔
      entry ∈ p13WindowBranchExcessComponentEntries ctx window ∧
        entry.tag = .crossWindow := by
  rw [p13WindowCrossWindowEntries, rightEntries, List.mem_filter]
  constructor
  · rintro ⟨member, notComponent⟩
    refine ⟨member, ?_⟩
    cases tagEquation : entry.tag <;>
      simp [tagEquation] at notComponent ⊢
  · rintro ⟨member, crossWindow⟩
    exact ⟨member, by simp [crossWindow]⟩

/-- Exact `A + X = 13` for this one selected window. -/
theorem p13WindowComponentCrossWindow_partition
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (window : P13AmbientCubicWindow ctx) :
    (p13WindowComponentEntries ctx window).length +
        (p13WindowCrossWindowEntries ctx window).length = 13 := by
  rw [p13WindowComponentEntries, p13WindowCrossWindowEntries,
    partition_length,
    p13WindowBranchExcessComponentEntries_length]

abbrev P13WindowComponentCrossWindowMajority
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (window : P13AmbientCubicWindow ctx) :=
  Outcome (p13WindowBranchExcessComponentEntries ctx window)
    (fun entry => entry.tag = .component) 7

/-- Exhaustive local `7`-of-`13` decision for one selected window. -/
noncomputable def runP13WindowComponentCrossWindowMajority
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (window : P13AmbientCubicWindow ctx) :
    P13WindowComponentCrossWindowMajority ctx window :=
  decideOdd (p13WindowBranchExcessComponentEntries ctx window)
    (fun entry => entry.tag = .component) 6
    (p13WindowBranchExcessComponentEntries_length ctx window)

theorem p13WindowComponentCrossWindowMajority_exhaustive
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (window : P13AmbientCubicWindow ctx) :
    7 ≤ (p13WindowComponentEntries ctx window).length ∨
      7 ≤ (p13WindowCrossWindowEntries ctx window).length := by
  cases runP13WindowComponentCrossWindowMajority ctx window with
  | leftMajority large => exact Or.inl large
  | rightMajority large => exact Or.inr large

/-- The visible universe is exactly the thirteen predecessor entries of the
one supplied window. -/
noncomputable def p13WindowComponentCrossWindowChecks
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (window : P13AmbientCubicWindow ctx) : Nat :=
  visibleChecks (p13WindowBranchExcessComponentEntries ctx window)

theorem p13WindowComponentCrossWindowChecks_eq_thirteen
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (window : P13AmbientCubicWindow ctx) :
    p13WindowComponentCrossWindowChecks ctx window = 13 := by
  exact p13WindowBranchExcessComponentEntries_length ctx window

namespace VerifiedP13BranchExcessComponentPrefix

variable {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
variable {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}

/-- Thin same-context execution from the verified component-entry prefix. -/
noncomputable def windowMajority
    (_prefix : VerifiedP13BranchExcessComponentPrefix ctx node21)
    (window : P13AmbientCubicWindow ctx) :
    P13WindowComponentCrossWindowMajority ctx window :=
  runP13WindowComponentCrossWindowMajority ctx window

theorem windowMajority_exhaustive
    (_prefix : VerifiedP13BranchExcessComponentPrefix ctx node21)
    (window : P13AmbientCubicWindow ctx) :
    7 ≤ (p13WindowComponentEntries ctx window).length ∨
      7 ≤ (p13WindowCrossWindowEntries ctx window).length :=
  p13WindowComponentCrossWindowMajority_exhaustive ctx window

end VerifiedP13BranchExcessComponentPrefix

end Erdos64EG.Internal
