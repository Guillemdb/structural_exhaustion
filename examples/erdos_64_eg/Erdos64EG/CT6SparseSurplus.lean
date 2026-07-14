import Erdos64EG.CT10P13LabelAlgebra
import StructuralExhaustion.Graph.SurplusPortActivity

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# CT6: ordered degree-surplus activity

This file is deliberately thin.  The reusable graph profile owns the failure
predicate, bounded vertex scan, first-failure semantics, active ledger, exact
surplus sum, and work bound.  Erdős supplies only the already verified
minimum-degree-three cycle problem and its deletion-criticality theorem.

This stage formalizes the excess-selector cardinality and the cubic endpoint
clause of manuscript nodes `[127]`--`[128]`.  It does not assert the later
return/suppression paths `Γ(p)` or the baseline spine demand at node `[129]`.
-/

abbrev fixedPackedInput
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  packedStaticInput.fixed ctx.G.Vertex

abbrev sparseSurplusSpec
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  Graph.SurplusPortActivity.spec (fixedPackedInput ctx)

abbrev sparseSurplusCapability
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  Graph.SurplusPortActivity.capability (fixedPackedInput ctx) ctx.G.object

abbrev sparseSurplusContext
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  Graph.SurplusPortActivity.context (fixedPackedInput ctx) ctx.G.object
    (packedStaticInput.fixedContext ctx).baseline

/-- The exact CT6 active-ledger run on the selected minimal graph. -/
def runSparseSurplusCT6
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  Graph.SurplusPortActivity.run (fixedPackedInput ctx) ctx.G.object
    (packedStaticInput.fixedContext ctx).baseline
    ((fixedPackedInput ctx).dart_has_tight_endpoint
      (packedStaticInput.fixedContext ctx))

theorem runSparseSurplusCT6_terminal
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    (runSparseSurplusCT6 ctx).execution.terminal = .activeLedger :=
  (runSparseSurplusCT6 ctx).terminal_eq

theorem runSparseSurplusCT6_trace
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    (runSparseSurplusCT6 ctx).execution.trace =
      [.entry, .firstFailureSearch, .activeLedgerTerminal] :=
  (runSparseSurplusCT6 ctx).trace_eq

/-- The CT6 ledger is exactly the manuscript degree-surplus sum. -/
theorem runSparseSurplusCT6_total_eq_sigma
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    (runSparseSurplusCT6 ctx).residual.total =
      (ctx.G.object.input.vertices.orderedValues.map
        (fun center => ctx.G.object.degree center - 3)).sum :=
  Graph.SurplusPortActivity.run_total_eq_surplus
    (fixedPackedInput ctx) ctx.G.object
    (packedStaticInput.fixedContext ctx).baseline
    ((fixedPackedInput ctx).dart_has_tight_endpoint
      (packedStaticInput.fixedContext ctx))

/-- Every incident edge at a high centre has a cubic opposite endpoint. -/
theorem sparseSurplus_highCenter_neighbor_cubic
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {center neighbor : ctx.G.Vertex}
    (centerHigh : 4 ≤ ctx.G.object.degree center)
    (adjacent : ctx.G.object.graph.Adj center neighbor) :
    ctx.G.object.degree neighbor = 3 :=
  Graph.SurplusPortActivity.run_highCenter_neighbor_cubic
    (fixedPackedInput ctx) ctx.G.object
    (packedStaticInput.fixedContext ctx).baseline
    ((fixedPackedInput ctx).dart_has_tight_endpoint
      (packedStaticInput.fixedContext ctx)) centerHigh adjacent

/-- The formal excess-port slot universe has cardinality exactly `σ(G)`. -/
theorem sparseSurplus_excessPortSlot_card
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    letI : FinEnum ctx.G.Vertex := ctx.G.object.input.vertices
    Fintype.card (Graph.SurplusPortActivity.ExcessPortSlot ctx.G.object) =
      (ctx.G.object.input.vertices.orderedValues.map
        (fun center => ctx.G.object.degree center - 3)).sum :=
  Graph.SurplusPortActivity.excessPortSlot_card_eq_surplus ctx.G.object

theorem runSparseSurplusCT6_checks_linear
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Graph.SurplusPortActivity.checkCount ctx.G.object ≤
      ctx.G.object.input.vertices.card + 1 :=
  Graph.SurplusPortActivity.checkCount_linear ctx.G.object

theorem runSparseSurplusCT6_primitiveChecks_quadratic
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Graph.SurplusPortActivity.primitiveCheckBound ctx.G.object ≤
      (ctx.G.object.input.vertices.card + 1) ^ 2 :=
  Graph.SurplusPortActivity.primitiveCheckBound_quadratic ctx.G.object

/-- Exact output of the rigorous CT6 surplus stage, retaining node `[18]`. -/
structure VerifiedSparseSurplusPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Prop where
  previous : VerifiedP13LabelAlgebraPrefix ctx
  terminal : (runSparseSurplusCT6 ctx).execution.terminal = .activeLedger
  trace : (runSparseSurplusCT6 ctx).execution.trace =
    [.entry, .firstFailureSearch, .activeLedgerTerminal]
  totalEqSigma : (runSparseSurplusCT6 ctx).residual.total =
    (ctx.G.object.input.vertices.orderedValues.map
      (fun center => ctx.G.object.degree center - 3)).sum
  cubicEndpoints : ∀ {center neighbor : ctx.G.Vertex},
    4 ≤ ctx.G.object.degree center →
    ctx.G.object.graph.Adj center neighbor →
    ctx.G.object.degree neighbor = 3

def verifiedSparseSurplusPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedP13LabelAlgebraPrefix ctx) :
    VerifiedSparseSurplusPrefix ctx where
  previous := previous
  terminal := runSparseSurplusCT6_terminal ctx
  trace := runSparseSurplusCT6_trace ctx
  totalEqSigma := runSparseSurplusCT6_total_eq_sigma ctx
  cubicEndpoints := sparseSurplus_highCenter_neighbor_cubic ctx

/-- Starting from the official counterexample boundary, retain the identical
minimal graph and execute the complete ordered surplus CT6 audit. -/
theorem exists_verifiedSparseSurplusPrefix {V : Type u}
    (object : Object V) (baseline : Baseline object)
    (avoids : ¬Target object) :
    ∃ ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u},
      PackedProblem.{u}.rank ctx.G ≤
          PackedProblem.{u}.rank (Graph.PackedFiniteObject.pack object) ∧
        VerifiedSparseSurplusPrefix.{u} ctx := by
  obtain ⟨ctx, rankLe, previous⟩ :=
    exists_verifiedP13LabelAlgebraPrefix object baseline avoids
  exact ⟨ctx, rankLe, verifiedSparseSurplusPrefix ctx previous⟩

end Erdos64EG.Internal
