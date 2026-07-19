import Erdos64EG.CT10P13MultiScaleCurvature
import StructuralExhaustion.Graph.InducedPathColdStubSelection

namespace Erdos64EG.Internal

open StructuralExhaustion
open StructuralExhaustion.Graph
open StructuralExhaustion.Graph.InducedPathWindowLedger

universe u

/-!
# Exact fixed-skeleton entry schedule

This is the first graph-owned producer on the non-Boolean route from node
`[21]` toward the fixed cold-skeleton analysis.  It traverses the exact CT12
selected-window order once.  Every selected window is classified from its
thirteen literal degree rows as either

* a first position of strict degree surplus, or
* an ambient-cubic window with its canonical first external-incidence stub.

The schedule is computed from the selected graph and packing.  No window,
cold-family, support, coverage ceiling, density estimate, or outcome schedule
is accepted from a caller.  This module deliberately stops before F2/F3
response semantics, bounded-overlap aggregation, or the node-`[24]` density
inequality.
-/

abbrev P13FixedSkeletonEntry
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  Sigma fun window : WindowIndex ctx.G.object =>
    InducedPathColdStubSelection.Entry ctx.G.object window

/-- The computed entry attached to one literal member of the selected
packing. -/
noncomputable def p13FixedSkeletonEntry
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (window : WindowIndex ctx.G.object) : P13FixedSkeletonEntry ctx :=
  ⟨window, InducedPathColdStubSelection.classify ctx.G.object
    (fun vertex =>
      ctx.baseline.trans (ctx.G.object.minDegree_le_degree vertex)) window⟩

/-- The graph-owned schedule in the exact selected-window order. -/
noncomputable def p13FixedSkeletonEntrySchedule
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    List (P13FixedSkeletonEntry ctx) :=
  (windowIndices ctx.G.object).orderedValues.map
    (p13FixedSkeletonEntry ctx)

/-- Node-`[21]` provenance for the computed schedule.  The schedule itself is
not a field, so an application cannot replace it by caller data. -/
structure VerifiedP13FixedSkeletonEntryPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx) : Type (u + 4) where
  previous : VerifiedP13MultiScaleCurvaturePrefix ctx
  samePrevious : previous = node21

def verifiedP13FixedSkeletonEntryPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx) :
    VerifiedP13FixedSkeletonEntryPrefix ctx node21 where
  previous := node21
  samePrevious := rfl

namespace VerifiedP13FixedSkeletonEntryPrefix

variable {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
variable {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}

/-- The only schedule exposed by the prefix is the canonical graph-owned
one. -/
noncomputable def entries
    (_verified : VerifiedP13FixedSkeletonEntryPrefix ctx node21) :
    List (P13FixedSkeletonEntry ctx) :=
  p13FixedSkeletonEntrySchedule ctx

/-- Projecting the dependent entries recovers the exact CT12 window order. -/
theorem entries_windows_exact
    (verified : VerifiedP13FixedSkeletonEntryPrefix ctx node21) :
    (verified.entries.map fun entry => entry.1) =
      (windowIndices ctx.G.object).orderedValues := by
  let windows := (windowIndices ctx.G.object).orderedValues
  change ((windows.map (p13FixedSkeletonEntry ctx)).map
      fun entry => entry.1) = windows
  induction windows with
  | nil => rfl
  | cons window rest ih =>
      simp [p13FixedSkeletonEntry, ih]

/-- Every literal selected window occurs in the computed schedule. -/
theorem entry_exists
    (verified : VerifiedP13FixedSkeletonEntryPrefix ctx node21)
    (window : WindowIndex ctx.G.object) :
    ∃ entry ∈ verified.entries, entry.1 = window := by
  refine ⟨p13FixedSkeletonEntry ctx window, ?_, rfl⟩
  simp only [entries, p13FixedSkeletonEntrySchedule, List.mem_map]
  exact ⟨window, (windowIndices ctx.G.object).mem_orderedValues window, rfl⟩

/-- The schedule contains exactly one entry per selected packing window. -/
theorem entries_length
    (verified : VerifiedP13FixedSkeletonEntryPrefix ctx node21) :
    verified.entries.length = p13 ctx := by
  rw [entries, p13FixedSkeletonEntrySchedule, List.length_map,
    FinEnum.orderedValues_length,
    windowIndex_card_eq_packingNumber]
  rfl

/-- Every computed entry exposes the honest local dichotomy.  In the cubic
case the canonical stub belongs to that very window. -/
theorem entry_exhaustive
    (verified : VerifiedP13FixedSkeletonEntryPrefix ctx node21)
    (entry : P13FixedSkeletonEntry ctx)
    (member : entry ∈ verified.entries) :
    (∃ position high,
        entry.2 = .high position high) ∨
      (∃ stub same,
        entry.2 = .cubic stub same) := by
  rcases entry with ⟨window, result⟩
  have exactResult : result =
      InducedPathColdStubSelection.classify ctx.G.object
        (fun vertex =>
          ctx.baseline.trans (ctx.G.object.minDegree_le_degree vertex))
        window := by
    have computed :
        InducedPathColdStubSelection.classify ctx.G.object
          (fun vertex =>
            ctx.baseline.trans (ctx.G.object.minDegree_le_degree vertex))
          window = result := by
      simpa [entries, p13FixedSkeletonEntrySchedule,
        p13FixedSkeletonEntry] using member
    exact computed.symm
  cases classified : InducedPathColdStubSelection.classify ctx.G.object
      (fun vertex =>
        ctx.baseline.trans (ctx.G.object.minDegree_le_degree vertex))
      window with
  | high position high =>
      left
      exact ⟨position, high, exactResult.trans classified⟩
  | cubic stub same =>
      right
      exact ⟨stub, same, exactResult.trans classified⟩

/-- A cubic entry carries the exact fifteen-stub and thirteen-branch-excess
arithmetic required by the fixed skeleton, with no asymptotics. -/
theorem cubic_entry_exact_counts
    (verified : VerifiedP13FixedSkeletonEntryPrefix ctx node21)
    (entry : P13FixedSkeletonEntry ctx)
    (_member : entry ∈ verified.entries)
    (stub : InducedPathColdCorridor.CubicStub ctx.G.object)
    (same : stub.window = entry.1)
    (_isCubic : entry.2 = .cubic stub same) :
    (∑ position : Fin 13,
        (externalNeighbors ctx.G.object entry.1 position).card) = 15 ∧
      (∑ position : Fin 13,
        (externalNeighbors ctx.G.object entry.1 position).card) - 2 = 13 := by
  have cubic : InducedPathColdLedger.AmbientCubic ctx.G.object entry.1 := by
    rw [← same]
    exact stub.cubic
  exact ⟨InducedPathColdLedger.external_stub_count_eq_fifteen
      ctx.G.object entry.1 cubic,
    InducedPathColdLedger.branchExcess_eq_thirteen
      ctx.G.object entry.1 cubic⟩

end VerifiedP13FixedSkeletonEntryPrefix

/-! ## Visible local work -/

/-- One degree/adjacency pass for the selected packing, plus at most one scan
of the existing token schedule for each selected window. -/
noncomputable def p13FixedSkeletonEntryChecks
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) : Nat :=
  InducedPathWindowLedger.checks ctx.G.object +
    packingNumber ctx.G.object * (tokens ctx.G.object).card

noncomputable def p13FixedSkeletonEntryScale
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) : Nat :=
  1 + ctx.G.object.input.vertices.card + packingNumber ctx.G.object +
    (tokens ctx.G.object).card

/-- The producer scans only the explicit selected-window and incidence
schedules and has a quadratic bound in their combined local size. -/
theorem p13FixedSkeletonEntryChecks_quadratic
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    p13FixedSkeletonEntryChecks ctx ≤
      14 * p13FixedSkeletonEntryScale ctx ^ 2 := by
  let scale := p13FixedSkeletonEntryScale ctx
  have vertexLe : ctx.G.object.input.vertices.card ≤ scale := by
    dsimp [scale, p13FixedSkeletonEntryScale]
    omega
  have packingLe : packingNumber ctx.G.object ≤ scale := by
    dsimp [scale, p13FixedSkeletonEntryScale]
    omega
  have tokenLe : (tokens ctx.G.object).card ≤ scale := by
    dsimp [scale, p13FixedSkeletonEntryScale]
    omega
  have windowChecks :=
    InducedPathWindowLedger.checks_le_thirteen_mul_square ctx.G.object
  have windowBound :
      InducedPathWindowLedger.checks ctx.G.object ≤ 13 * scale ^ 2 :=
    windowChecks.trans (Nat.mul_le_mul_left 13
      (Nat.pow_le_pow_left vertexLe 2))
  have tokenBound :
      packingNumber ctx.G.object * (tokens ctx.G.object).card ≤ scale ^ 2 := by
    simpa [pow_two] using Nat.mul_le_mul packingLe tokenLe
  unfold p13FixedSkeletonEntryChecks
  nlinarith

end Erdos64EG.Internal
