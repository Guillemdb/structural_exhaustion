import Erdos64EG.P13WeightedColdBranchExcess
import StructuralExhaustion.Graph.InducedPathRestrictedColdSkeleton

namespace Erdos64EG.Internal

open StructuralExhaustion
open StructuralExhaustion.Graph

universe u

/-!
# Exact weighted-cold deletion entry

This is the paper-faithful replacement for the broader ambient-cubic skeleton
adapter.  The deleted support is built only from the exact weighted-cold cubic
list.  A hot ambient-cubic selected window is therefore not deleted merely
because it is ambient-cubic.
-/

variable {ctx : Core.MinimalCounterexampleContext
  PackedProblem.{u} PackedTarget.{u}}
variable {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}

abbrev P13WeightedColdBranchExcessSource :=
  Sigma fun window : P13WeightedColdCubicWindow ctx node21 =>
    P13WeightedColdBranchExcessStub window

/-- Exact finite selected-window index family underlying the weighted-cold
cubic ledger. -/
noncomputable def p13WeightedColdCubicWindowIndices :
    Finset (InducedPathWindowLedger.WindowIndex ctx.G.object) := by
  classical
  exact ((p13WeightedColdCubicWindows
      (ctx := ctx) (node21 := node21)).map fun window =>
        p13WeightedWindowIndex window.cold.window).toFinset

theorem p13WeightedColdCubicWindowIndices_cubic
    (window : InducedPathWindowLedger.WindowIndex ctx.G.object)
    (member : window ∈ p13WeightedColdCubicWindowIndices
      (ctx := ctx) (node21 := node21)) :
    InducedPathColdLedger.AmbientCubic ctx.G.object window := by
  classical
  rw [p13WeightedColdCubicWindowIndices, List.mem_toFinset] at member
  rcases List.mem_map.mp member with ⟨cold, _coldMem, equal⟩
  rw [← equal]
  exact cold.cubic

/-- The node21-indexed family deleted by the paper's `X_cold`. -/
noncomputable def p13WeightedColdWindowFamily :
    InducedPathRestrictedColdSkeleton.CubicWindowFamily ctx.G.object where
  windows := p13WeightedColdCubicWindowIndices
    (ctx := ctx) (node21 := node21)
  cubic := p13WeightedColdCubicWindowIndices_cubic
    (ctx := ctx) (node21 := node21)

/-- The exact `X_cold` vertex union. -/
noncomputable def p13WeightedColdDeletedVertices : Finset ctx.G.Vertex :=
  InducedPathRestrictedColdSkeleton.deletedWindowVertices
    (p13WeightedColdWindowFamily (ctx := ctx) (node21 := node21))

private theorem source_window_mem_cubic_list
    (source : P13WeightedColdBranchExcessSource
      (ctx := ctx) (node21 := node21))
    (member : source ∈ p13WeightedColdBranchExcessSchedule
      (ctx := ctx) (node21 := node21)) :
    source.1 ∈ p13WeightedColdCubicWindows
      (ctx := ctx) (node21 := node21) := by
  rw [p13WeightedColdBranchExcessSchedule, List.mem_flatMap] at member
  rcases member with ⟨window, windowMem, sourceMem⟩
  rw [List.mem_map] at sourceMem
  rcases sourceMem with ⟨stub, _stubMem, equal⟩
  cases equal
  exact windowMem

theorem source_stub_window_mem_cold_family
    (source : P13WeightedColdBranchExcessSource
      (ctx := ctx) (node21 := node21))
    (member : source ∈ p13WeightedColdBranchExcessSchedule
      (ctx := ctx) (node21 := node21)) :
    source.2.stub.window ∈
      (p13WeightedColdWindowFamily
        (ctx := ctx) (node21 := node21)).windows := by
  classical
  change source.2.stub.window ∈ p13WeightedColdCubicWindowIndices
    (ctx := ctx) (node21 := node21)
  rw [source.2.sameWindow]
  unfold p13WeightedColdCubicWindowIndices
  rw [List.mem_toFinset, List.mem_map]
  exact ⟨source.1, source_window_mem_cubic_list source member, rfl⟩

abbrev P13WeightedColdRestrictedRoute
    (source : P13WeightedColdBranchExcessSource
      (ctx := ctx) (node21 := node21))
    (sourceMember : source ∈ p13WeightedColdBranchExcessSchedule
      (ctx := ctx) (node21 := node21)) :=
  InducedPathRestrictedColdSkeleton.EntryResult
    (p13WeightedColdWindowFamily (ctx := ctx) (node21 := node21))
    source.2.stub (source_stub_window_mem_cold_family source sourceMember)

/-- One literal node-[152] source and its exact cold-only endpoint decision. -/
structure P13WeightedColdRestrictedEntry
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx) : Type (u + 3) where
  source : P13WeightedColdBranchExcessSource (ctx := ctx) (node21 := node21)
  sourceMember : source ∈ p13WeightedColdBranchExcessSchedule
    (ctx := ctx) (node21 := node21)
  route : P13WeightedColdRestrictedRoute source sourceMember
  routeExact : route = InducedPathRestrictedColdSkeleton.route
    (p13WeightedColdWindowFamily (ctx := ctx) (node21 := node21))
    source.2.stub (source_stub_window_mem_cold_family source sourceMember)

/-- Execute the cold-only endpoint dichotomy over the exact node-[152] list. -/
noncomputable def p13WeightedColdRestrictedEntries :
    List (P13WeightedColdRestrictedEntry ctx node21) :=
  (p13WeightedColdBranchExcessSchedule
    (ctx := ctx) (node21 := node21)).attach.map fun source =>
      ⟨source.1, source.2,
        InducedPathRestrictedColdSkeleton.route
          (p13WeightedColdWindowFamily (ctx := ctx) (node21 := node21))
          source.1.2.stub
          (source_stub_window_mem_cold_family source.1 source.2),
        rfl⟩

theorem p13WeightedColdRestrictedEntries_length :
    (p13WeightedColdRestrictedEntries
      (ctx := ctx) (node21 := node21)).length =
      (p13WeightedColdBranchExcessSchedule
        (ctx := ctx) (node21 := node21)).length := by
  simp [p13WeightedColdRestrictedEntries]

/-- The cold-only endpoint decision consumes the literal node-`[152]` source
schedule without dropping, reordering, or duplicating an occurrence. -/
theorem p13WeightedColdRestrictedEntries_sources :
    (p13WeightedColdRestrictedEntries
      (ctx := ctx) (node21 := node21)).map P13WeightedColdRestrictedEntry.source =
      p13WeightedColdBranchExcessSchedule
        (ctx := ctx) (node21 := node21) := by
  simp [p13WeightedColdRestrictedEntries]

/-- In particular, the source projection of the exact entry schedule is
duplicate-free. -/
theorem p13WeightedColdRestrictedEntries_sources_nodup :
    ((p13WeightedColdRestrictedEntries
      (ctx := ctx) (node21 := node21)).map
        P13WeightedColdRestrictedEntry.source).Nodup := by
  rw [p13WeightedColdRestrictedEntries_sources]
  exact p13WeightedColdBranchExcessSchedule_nodup

theorem P13WeightedColdRestrictedEntry.sameWindow
    (entry : P13WeightedColdRestrictedEntry ctx node21) :
    entry.source.2.stub.window =
      p13WeightedWindowIndex entry.source.1.cold.window :=
  entry.source.2.sameWindow

theorem P13WeightedColdRestrictedEntry.route_exhaustive
    (entry : P13WeightedColdRestrictedEntry ctx node21) :
    (∃ boundary tokenExact,
      entry.route = .componentBoundary boundary tokenExact) ∨
    (∃ residual, entry.route = .crossWindow residual) := by
  rw [entry.routeExact]
  exact InducedPathRestrictedColdSkeleton.route_exhaustive
    (p13WeightedColdWindowFamily (ctx := ctx) (node21 := node21))
    entry.source.2.stub
    (source_stub_window_mem_cold_family entry.source entry.sourceMember)

inductive P13WeightedColdRestrictedTag
  | componentBoundary
  | crossWindow
  deriving DecidableEq

def P13WeightedColdRestrictedEntry.tag
    (entry : P13WeightedColdRestrictedEntry ctx node21) :
    P13WeightedColdRestrictedTag :=
  match entry.route with
  | .componentBoundary _ _ => .componentBoundary
  | .crossWindow _ => .crossWindow

noncomputable def p13WeightedColdRestrictedEntriesWithTag
    (tag : P13WeightedColdRestrictedTag) :
    List (P13WeightedColdRestrictedEntry ctx node21) :=
  (p13WeightedColdRestrictedEntries
    (ctx := ctx) (node21 := node21)).filter fun entry => entry.tag = tag

private theorem twoTagPartitionLength
    (entries : List (P13WeightedColdRestrictedEntry ctx node21)) :
    (entries.filter fun entry =>
        entry.tag = P13WeightedColdRestrictedTag.componentBoundary).length +
      (entries.filter fun entry =>
        entry.tag = P13WeightedColdRestrictedTag.crossWindow).length =
      entries.length := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
      cases tagEquation : entry.tag <;> simp [tagEquation] <;> omega

theorem p13WeightedColdRestrictedEntries_partition :
    (p13WeightedColdRestrictedEntriesWithTag
      (ctx := ctx) (node21 := node21) .componentBoundary).length +
      (p13WeightedColdRestrictedEntriesWithTag
        (ctx := ctx) (node21 := node21) .crossWindow).length =
      (p13WeightedColdBranchExcessSchedule
        (ctx := ctx) (node21 := node21)).length := by
  rw [p13WeightedColdRestrictedEntriesWithTag,
    p13WeightedColdRestrictedEntriesWithTag,
    twoTagPartitionLength,
    p13WeightedColdRestrictedEntries_length]

/-- One cold-union membership test per exact source. -/
noncomputable def p13WeightedColdRestrictedEntryChecks : Nat :=
  (p13WeightedColdRestrictedEntries
    (ctx := ctx) (node21 := node21)).length

theorem p13WeightedColdRestrictedEntryChecks_linear :
    p13WeightedColdRestrictedEntryChecks
      (ctx := ctx) (node21 := node21) ≤
      ctx.G.object.input.vertices.card := by
  have cubicLeCold :
      (p13WeightedColdCubicWindows
        (ctx := ctx) (node21 := node21)).length ≤
        (p13SequentialWeightedColdWindows ctx node21).length := by
    have partition := p13WeightedCold_cubic_nonCubic_length
      (ctx := ctx) (node21 := node21)
    omega
  have coldLePacking :
      (p13SequentialWeightedColdWindows ctx node21).length ≤ p13 ctx := by
    have partition := p13SequentialWeightedHotCount_add_coldCount ctx node21
    omega
  calc
    p13WeightedColdRestrictedEntryChecks
        (ctx := ctx) (node21 := node21) =
        13 * (p13WeightedColdCubicWindows
          (ctx := ctx) (node21 := node21)).length := by
      rw [p13WeightedColdRestrictedEntryChecks,
        p13WeightedColdRestrictedEntries_length,
        p13WeightedColdBranchExcessSchedule_length]
    _ ≤ 13 * p13 ctx := Nat.mul_le_mul_left 13
      (cubicLeCold.trans coldLePacking)
    _ ≤ ctx.G.object.input.vertices.card :=
      thirteen_mul_p13_le_vertexCount ctx

end Erdos64EG.Internal
