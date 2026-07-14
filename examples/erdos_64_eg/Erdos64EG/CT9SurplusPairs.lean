import Erdos64EG.CT6SparseSurplus

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# CT9: exact surplus-pair availability

The registered CT6-to-CT9 route consumes the actual active-ledger residual.
Its local item universe is the exact dependent family of surplus slots.  CT9
uses one capacity-one label: its bounded branch proves that at most one slot
exists, while its overload branch returns two distinct slots.  Later
free/blocker semantics are not introduced here.
-/

abbrev surplusPairCapability
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  Graph.SurplusPortActivity.pairCapability (fixedPackedInput ctx) ctx.G.object

abbrev surplusPairInput
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  Graph.SurplusPortActivity.pairInput (fixedPackedInput ctx) ctx.G.object
    (packedStaticInput.fixedContext ctx).baseline
    ((fixedPackedInput ctx).dart_has_tight_endpoint
      (packedStaticInput.fixedContext ctx))

/-- The exact CT9 execution materialized through the registered route. -/
def runSurplusPairCT9
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  Graph.SurplusPortActivity.pairResult (fixedPackedInput ctx) ctx.G.object
    (packedStaticInput.fixedContext ctx).baseline
    ((fixedPackedInput ctx).dart_has_tight_endpoint
      (packedStaticInput.fixedContext ctx))

/-- The CT transition retains the identical packed graph, baseline, and
branch state. -/
theorem surplusPairRoute_context_preserved
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    (surplusPairInput ctx).context = sparseSurplusContext ctx :=
  Graph.SurplusPortActivity.pairInput_context_preserved
    (fixedPackedInput ctx) ctx.G.object
    (packedStaticInput.fixedContext ctx).baseline
    ((fixedPackedInput ctx).dart_has_tight_endpoint
      (packedStaticInput.fixedContext ctx))

theorem surplusPairRoute_id
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    ((Routes.CT6ToCT9.rule (surplusPairCapability ctx)
      (Graph.SurplusPortActivity.pairAdapter
        (fixedPackedInput ctx) ctx.G.object
        (packedStaticInput.fixedContext ctx).baseline
        ((fixedPackedInput ctx).dart_has_tight_endpoint
          (packedStaticInput.fixedContext ctx)))).generate
      (runSparseSurplusCT6 ctx).residual ()).routeId =
        "CT6.residual.activeLedger->CT9" :=
  Graph.SurplusPortActivity.pairRoute_id
    (fixedPackedInput ctx) ctx.G.object
    (packedStaticInput.fixedContext ctx).baseline
    ((fixedPackedInput ctx).dart_has_tight_endpoint
      (packedStaticInput.fixedContext ctx))

/-- The routed CT9 item count is exactly `σ(G)`. -/
theorem surplusPair_itemCount_eq_sigma
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    (surplusPairInput ctx).items.values.length =
      (ctx.G.object.input.vertices.orderedValues.map
        (fun center => ctx.G.object.degree center - 3)).sum :=
  Graph.SurplusPortActivity.pairItemCount_eq_surplus
    (fixedPackedInput ctx) ctx.G.object
    (packedStaticInput.fixedContext ctx).baseline
    ((fixedPackedInput ctx).dart_has_tight_endpoint
      (packedStaticInput.fixedContext ctx))

theorem runSurplusPairCT9_verified
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    (runSurplusPairCT9 ctx).outcome.Valid :=
  CT9.run_verified (surplusPairCapability ctx) (surplusPairInput ctx)

theorem runSurplusPairCT9_traceValid
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    CT9.Graph.ValidTrace (surplusPairCapability ctx) (surplusPairInput ctx)
      (runSurplusPairCT9 ctx).trace :=
  CT9.run_trace_valid (surplusPairCapability ctx) (surplusPairInput ctx)

theorem runSurplusPairCT9_total
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    ∃ result : CT9.ExecutionResult (surplusPairCapability ctx)
        (surplusPairInput ctx),
      result.outcome.Valid ∧
        CT9.Graph.ValidTrace (surplusPairCapability ctx)
          (surplusPairInput ctx) result.trace :=
  CT9.run_total (surplusPairCapability ctx) (surplusPairInput ctx)

/-- Exact state-space split from the terminal-indexed CT9 outcome. -/
def surplusPairDecision
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  Graph.SurplusPortActivity.pairDecision
    (fixedPackedInput ctx) ctx.G.object
    (packedStaticInput.fixedContext ctx).baseline
    ((fixedPackedInput ctx).dart_has_tight_endpoint
      (packedStaticInput.fixedContext ctx))

/-- On the branch `2 ≤ σ(G)`, the exact CT9 run reaches overload. -/
def runSurplusPairCT9OfTwoLeSigma
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (twoLe : 2 ≤
      (ctx.G.object.input.vertices.orderedValues.map
        (fun center => ctx.G.object.degree center - 3)).sum) :
    CT9.OverloadedRun (surplusPairCapability ctx) (surplusPairInput ctx) := by
  apply Graph.SurplusPortActivity.pairRunOfTwoLe
  rwa [surplusPair_itemCount_eq_sigma ctx]

/-- Two distinct surplus slots selected by CT9 on the nontrivial-surplus
branch. -/
def surplusPairOfTwoLeSigma
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (twoLe : 2 ≤
      (ctx.G.object.input.vertices.orderedValues.map
        (fun center => ctx.G.object.degree center - 3)).sum) :=
  CT9.OverloadedRun.sameLabelPairOfCapacityOne
    (surplusPairCapability ctx) (surplusPairInput ctx)
    (runSurplusPairCT9OfTwoLeSigma ctx twoLe) rfl

theorem surplusPairOfTwoLeSigma_distinct
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (twoLe : 2 ≤
      (ctx.G.object.input.vertices.orderedValues.map
        (fun center => ctx.G.object.degree center - 3)).sum) :
    (surplusPairOfTwoLeSigma ctx twoLe).first ≠
      (surplusPairOfTwoLeSigma ctx twoLe).second :=
  (surplusPairOfTwoLeSigma ctx twoLe).distinct

theorem runSurplusPairCT9_checks_linear
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    (surplusPairInput ctx).items.values.length ≤
      (surplusPairInput ctx).items.values.length + 1 :=
  Graph.SurplusPortActivity.pairChecks_linear
    (fixedPackedInput ctx) ctx.G.object
    (packedStaticInput.fixedContext ctx).baseline
    ((fixedPackedInput ctx).dart_has_tight_endpoint
      (packedStaticInput.fixedContext ctx))

/-- Exact prefix through the CT6-to-CT9 transition. -/
structure VerifiedSurplusPairPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Prop where
  previous : VerifiedSparseSurplusPrefix ctx
  routeId :
    ((Routes.CT6ToCT9.rule (surplusPairCapability ctx)
      (Graph.SurplusPortActivity.pairAdapter
        (fixedPackedInput ctx) ctx.G.object
        (packedStaticInput.fixedContext ctx).baseline
        ((fixedPackedInput ctx).dart_has_tight_endpoint
          (packedStaticInput.fixedContext ctx)))).generate
      (runSparseSurplusCT6 ctx).residual ()).routeId =
        "CT6.residual.activeLedger->CT9"
  verified : (runSurplusPairCT9 ctx).outcome.Valid
  traceValid : CT9.Graph.ValidTrace (surplusPairCapability ctx)
    (surplusPairInput ctx) (runSurplusPairCT9 ctx).trace

def verifiedSurplusPairPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedSparseSurplusPrefix ctx) :
    VerifiedSurplusPairPrefix ctx where
  previous := previous
  routeId := surplusPairRoute_id ctx
  verified := runSurplusPairCT9_verified ctx
  traceValid := runSurplusPairCT9_traceValid ctx

theorem exists_verifiedSurplusPairPrefix {V : Type u}
    (object : Object V) (baseline : Baseline object)
    (avoids : ¬Target object) :
    ∃ ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u},
      PackedProblem.{u}.rank ctx.G ≤
          PackedProblem.{u}.rank (Graph.PackedFiniteObject.pack object) ∧
        VerifiedSurplusPairPrefix.{u} ctx := by
  obtain ⟨ctx, rankLe, previous⟩ :=
    exists_verifiedSparseSurplusPrefix object baseline avoids
  exact ⟨ctx, rankLe, verifiedSurplusPairPrefix ctx previous⟩

end Erdos64EG.Internal
