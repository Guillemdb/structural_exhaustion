import Erdos64EG.CT12InducedP13Packing

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Nodes `[25]` and `[26]`: the exact remainder residual

These nodes are the local bookkeeping handoff from the preceding window-density
branch.  The predecessor supplies a finite coverage ceiling for the already
selected CT12 packing.  The handoff converts that ceiling into the matching
remainder floor and retains the packing-derived hereditary `P₁₃`-freeness on
the identical selected graph.  It does not execute the still-separate density
proof of node `[24]`.
-/

/-- Exact finite output required from the predecessor density branch.  The
quantity `windowCeiling` is the finite upper bound on the selected packing
produced by node `[24]`; it does not assume the remainder conclusion of nodes
`[25]`--`[26]`. -/
structure P13CoverageResidual
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedP13PackingPrefix ctx) where
  windowCeiling : Nat
  packing_le : p13 ctx ≤ windowCeiling

/-- Exact natural-number remainder floor determined by the predecessor's
packing ceiling. -/
def P13CoverageResidual.remainderFloor
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {previous : VerifiedP13PackingPrefix ctx}
    (density : P13CoverageResidual ctx previous) : Nat :=
  ctx.G.object.input.vertices.card - 13 * density.windowCeiling

/-- Complete local output displayed at node `[25]`. -/
structure VerifiedP13RemainderResidual
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedP13PackingPrefix ctx)
    (density : P13CoverageResidual ctx previous) : Type (u + 2) where
  packing : VerifiedP13PackingPrefix ctx
  exactPartition :
    (p13RemainderVertices ctx).card + 13 * p13 ctx =
      ctx.G.object.input.vertices.card
  large : density.remainderFloor ≤ (p13RemainderVertices ctx).card
  remainderFree : Graph.InducedPathFree (p13Remainder ctx).graph 13
  componentwiseFree : ∀ vertices : Set (P13RemainderVertex ctx),
    Graph.InducedPathFree ((p13Remainder ctx).graph.induce vertices) 13
  noInternalThreeCore : (p13Remainder ctx).InternalMinDegreeFree 3
  noInternalSubgraphThreeCore :
    ¬(p13Remainder ctx).HasInternalSubgraphMinDegreeAtLeast 3

/-- Construct node `[25]` from the exact predecessor coverage residual and the
already verified CT12 packing output on the same context. -/
noncomputable def verifiedP13RemainderResidual
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedP13PackingPrefix ctx)
    (density : P13CoverageResidual ctx previous) :
    VerifiedP13RemainderResidual ctx previous density where
  packing := previous
  exactPartition := p13Remainder_partition ctx
  large := Graph.InducedPathPacking.remainder_card_ge_of_packingNumber_le
    ctx.G.object 13 (by decide) density.windowCeiling density.packing_le
  remainderFree := p13Remainder_free ctx
  componentwiseFree := p13Remainder_componentwise_free ctx
  noInternalThreeCore := previous.2.output.added.noInternalThreeCore
  noInternalSubgraphThreeCore :=
    previous.2.output.added.noInternalSubgraphThreeCore

/-- Node `[25]` retains the exact CT12 predecessor, rather than rebuilding a
look-alike packing or remainder. -/
def p13RemainderResidual_previous
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedP13PackingPrefix ctx)
    (density : P13CoverageResidual ctx previous)
    (verified : VerifiedP13RemainderResidual ctx previous density) :
    VerifiedP13PackingPrefix ctx :=
  verified.packing

/-- The large-remainder clause is derived from packed coverage. -/
theorem p13Remainder_large
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedP13PackingPrefix ctx)
    (density : P13CoverageResidual ctx previous) :
    density.remainderFloor ≤ (p13RemainderVertices ctx).card :=
  (verifiedP13RemainderResidual ctx previous density).large

/-- Node `[26]` is the cross-panel continuation of exactly node `[25]`; no
new graph, packing, remainder, or bound is introduced at the panel boundary. -/
abbrev VerifiedP13RemainderContinuation
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedP13PackingPrefix ctx)
    (density : P13CoverageResidual ctx previous) :=
  VerifiedP13RemainderResidual ctx previous density

def p13Remainder_node26_exact
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedP13PackingPrefix ctx)
    (density : P13CoverageResidual ctx previous)
    (verified : VerifiedP13RemainderResidual ctx previous density) :
    VerifiedP13RemainderContinuation ctx previous density :=
  verified

end Erdos64EG.Internal
