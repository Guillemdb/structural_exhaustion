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

abbrev sparseSurplusEntry
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  (sparseSurplusCapability ctx).executableInterface

/-- The only problem-specific data for the CT10→CT6 manuscript edge. -/
abbrev sparseSurplusAdapter
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Routes.Accumulated.Adapter (VerifiedP13LabelAlgebraPrefix ctx)
      (sparseSurplusEntry ctx) :=
  Graph.SurplusPortActivity.activityAdapter
    (Source := VerifiedP13LabelAlgebraPrefix ctx)
    (fixedPackedInput ctx) ctx.G.object
    (packedStaticInput.fixedContext ctx).baseline

abbrev sparseSurplusTransition
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  Routes.Accumulated.transition (sourceTactic := .ct10)
    (sparseSurplusEntry ctx) (sparseSurplusAdapter ctx)

abbrev SparseSurplusSource
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  Core.Routing.ResidualStage .ct10 (VerifiedP13LabelAlgebraPrefix ctx)

abbrev SparseSurplusEnabledStage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (source : SparseSurplusSource ctx) :=
  Routes.Accumulated.OutputLedger
    (sparseSurplusEntry ctx) (sparseSurplusAdapter ctx) source

/-- Execute CT6 from the literal complete node-[18] ledger. -/
def sparseSurplusTransitionStage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (source : SparseSurplusSource ctx) : SparseSurplusEnabledStage ctx source :=
  Routes.Accumulated.advanceCurrent (sparseSurplusEntry ctx)
    (sparseSurplusAdapter ctx) source

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

/-- Mathematical consequences attached to the literal transitioned CT6
execution.  The active residual is extracted from that exact target result. -/
structure SparseSurplusFacts
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {source : SparseSurplusSource ctx}
    (stage : SparseSurplusEnabledStage ctx source) : Prop where
  terminal : stage.targetResult.terminal = .activeLedger
  trace : stage.targetResult.trace =
    [.entry, .firstFailureSearch, .activeLedgerTerminal]
  totalEqSigma :
    (stage.targetResult.activeLedgerResidual_of_terminal_eq terminal).total =
      (ctx.G.object.input.vertices.orderedValues.map
        (fun center => ctx.G.object.degree center - 3)).sum
  cubicEndpoints : ∀ {center neighbor : ctx.G.Vertex},
    4 ≤ ctx.G.object.degree center →
    ctx.G.object.graph.Adj center neighbor →
    ctx.G.object.degree neighbor = 3

abbrev SparseSurplusLedger
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (source : SparseSurplusSource ctx) :=
  Core.Routing.LedgerExtension (SparseSurplusEnabledStage ctx source)
    (SparseSurplusFacts ctx)

/-- Exact output of the rigorous CT10→CT6 edge and its same-CT theorem
extension. -/
abbrev VerifiedSparseSurplusPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  Sigma (SparseSurplusLedger ctx)

def sparseSurplusFacts
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (source : SparseSurplusSource ctx) :
    SparseSurplusFacts ctx (sparseSurplusTransitionStage ctx source) where
  terminal := runSparseSurplusCT6_terminal ctx
  trace := runSparseSurplusCT6_trace ctx
  totalEqSigma := runSparseSurplusCT6_total_eq_sigma ctx
  cubicEndpoints := sparseSurplus_highCenter_neighbor_cubic ctx

def verifiedSparseSurplusPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedP13LabelAlgebraPrefix ctx) :
    VerifiedSparseSurplusPrefix ctx :=
  let source : SparseSurplusSource ctx :=
    Core.Routing.ResidualStage.exact (tactic := .ct10) previous
  let stage := sparseSurplusTransitionStage ctx source
  ⟨source, ⟨stage, sparseSurplusFacts ctx source⟩⟩

/-- Canonical complete CT6 ledger for every downstream edge. -/
def sparseSurplusLedgerStage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (verified : VerifiedSparseSurplusPrefix ctx) :=
  verified.2.previous.ledgerStage.extend verified.2.added

/-- The active residual extracted from the literal CT6 target result. -/
def sparseSurplusResidual
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (verified : VerifiedSparseSurplusPrefix ctx) :=
  verified.2.previous.targetResult.activeLedgerResidual_of_terminal_eq
    verified.2.added.terminal

theorem VerifiedSparseSurplusPrefix.cubicEndpoints
    (verified : VerifiedSparseSurplusPrefix ctx) :
    ∀ {center neighbor : ctx.G.Vertex},
      4 ≤ ctx.G.object.degree center →
      ctx.G.object.graph.Adj center neighbor →
      ctx.G.object.degree neighbor = 3 :=
  verified.2.added.cubicEndpoints

/-- Starting from the official counterexample boundary, retain the identical
minimal graph and execute the complete ordered surplus CT6 audit. -/
theorem exists_verifiedSparseSurplusPrefix {V : Type u}
    (object : Object V) (baseline : Baseline object)
    (avoids : ¬Target object) :
    ∃ ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u},
      ∃ _ : VerifiedSparseSurplusPrefix ctx,
        PackedProblem.{u}.rank ctx.G ≤
          PackedProblem.{u}.rank (Graph.PackedFiniteObject.pack object) := by
  obtain ⟨ctx, previous, rankLe⟩ :=
    exists_verifiedP13LabelAlgebraPrefix object baseline avoids
  exact ⟨ctx, verifiedSparseSurplusPrefix ctx previous, rankLe⟩

end Erdos64EG.Internal
