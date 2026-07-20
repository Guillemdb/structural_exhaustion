import Erdos64EG.Shared.CT6SparseSurplus

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# CT9: exact surplus-pair availability

The registered CT6-to-CT9 transition consumes the actual active-ledger residual.
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

abbrev surplusPairTransition
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  Graph.SurplusPortActivity.pairTransition (fixedPackedInput ctx) ctx.G.object
    (packedStaticInput.fixedContext ctx).baseline
    ((fixedPackedInput ctx).dart_has_tight_endpoint
      (packedStaticInput.fixedContext ctx))

abbrev SurplusPairSource
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedSparseSurplusPrefix ctx) :=
  Core.Routing.ResidualStage .ct6 (SparseSurplusLedger ctx previous.1)

def surplusPairCurrent
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedSparseSurplusPrefix ctx)
    (ledger : SparseSurplusLedger ctx previous.1) :=
  ledger.previous.targetResult.activeLedgerResidual_of_terminal_eq
    ledger.added.terminal

abbrev SurplusPairEnabledStage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedSparseSurplusPrefix ctx) :=
  (surplusPairTransition ctx).OutputLedger (surplusPairCurrent ctx previous)
    (sparseSurplusLedgerStage ctx previous)

/-- Exact prefix through the CT6→CT9 transition.  Its enabled stage retains
the literal complete transitioned CT6 ledger. -/
abbrev VerifiedSurplusPairPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  Sigma fun previous : VerifiedSparseSurplusPrefix ctx =>
    Core.Routing.ResidualStage .ct9 (SurplusPairEnabledStage ctx previous)

/-- The exact CT9 execution returned by the registered transition. -/
def runSurplusPairCT9
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (verified : VerifiedSurplusPairPrefix ctx) :=
  verified.2.output.targetResult

/-- Full CT9 ledger used by the helper CT1 attachment. -/
def surplusPairLedger
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (verified : VerifiedSurplusPairPrefix ctx) :=
  verified.2

/-- The CT transition retains the identical packed graph, baseline, and
branch state. -/
theorem surplusPairTransition_context_preserved
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    (surplusPairInput ctx).context = sparseSurplusContext ctx :=
  Graph.SurplusPortActivity.pairInput_context_preserved
    (fixedPackedInput ctx) ctx.G.object
    (packedStaticInput.fixedContext ctx).baseline
    ((fixedPackedInput ctx).dart_has_tight_endpoint
      (packedStaticInput.fixedContext ctx))

theorem surplusPairTransition_profile_id
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    (surplusPairTransition ctx).profileId =
        "CT6.residual.activeLedger->CT9" :=
  Graph.SurplusPortActivity.pairTransition_profile_id
    (fixedPackedInput ctx) ctx.G.object
    (packedStaticInput.fixedContext ctx).baseline
    ((fixedPackedInput ctx).dart_has_tight_endpoint
      (packedStaticInput.fixedContext ctx))

/-- The transitioned CT9 item count is exactly `σ(G)`. -/
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
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (verified : VerifiedSurplusPairPrefix ctx) :
    (runSurplusPairCT9 ctx verified).outcome.Valid :=
  (runSurplusPairCT9 ctx verified).verified

theorem runSurplusPairCT9_traceValid
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (verified : VerifiedSurplusPairPrefix ctx) :
    CT9.Graph.ValidTrace (surplusPairCapability ctx) (surplusPairInput ctx)
      (runSurplusPairCT9 ctx verified).trace :=
  (runSurplusPairCT9 ctx verified).traceValid

theorem runSurplusPairCT9_total
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (verified : VerifiedSurplusPairPrefix ctx) :
    ∃ result : CT9.ExecutionResult (surplusPairCapability ctx)
        (surplusPairInput ctx),
      result.outcome.Valid ∧
        CT9.Graph.ValidTrace (surplusPairCapability ctx)
          (surplusPairInput ctx) result.trace :=
  ⟨runSurplusPairCT9 ctx verified,
    (runSurplusPairCT9 ctx verified).verified,
    (runSurplusPairCT9 ctx verified).traceValid⟩

/-- If the exact surplus-slot schedule has at least two members, the literal
transition result cannot be the capacity-one bounded terminal. -/
theorem runSurplusPairCT9_terminal_overloaded_of_twoLe
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (verified : VerifiedSurplusPairPrefix ctx)
    (twoLe : 2 ≤
      (ctx.G.object.input.vertices.orderedValues.map
        (fun center => ctx.G.object.degree center - 3)).sum) :
    (runSurplusPairCT9 ctx verified).terminal = .overloaded := by
  generalize resultEq : runSurplusPairCT9 ctx verified = result
  cases result with
  | mk terminal path outcome =>
      cases outcome with
      | overloaded residual => rfl
      | bounded certificate =>
          exfalso
          have small := certificate.cardinality_le_totalCapacity
          change (surplusPairInput ctx).items.values.length ≤ 1 at small
          rw [surplusPair_itemCount_eq_sigma ctx] at small
          omega

/-- Exact state-space split from the terminal-indexed CT9 outcome. -/
def surplusPairDecision
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (verified : VerifiedSurplusPairPrefix ctx) :=
  Graph.SurplusPortActivity.pairDecisionOfResult
    (fixedPackedInput ctx) ctx.G.object
    (packedStaticInput.fixedContext ctx).baseline
    ((fixedPackedInput ctx).dart_has_tight_endpoint
      (packedStaticInput.fixedContext ctx))
    (runSurplusPairCT9 ctx verified)

/-- Two distinct surplus slots extracted from the literal transitioned CT9
result on the nontrivial-surplus branch.  A bounded result is impossible
because its certificate would bound the exact item family by one. -/
def surplusPairOfTwoLeSigma
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (verified : VerifiedSurplusPairPrefix ctx)
    (twoLe : 2 ≤
      (ctx.G.object.input.vertices.orderedValues.map
        (fun center => ctx.G.object.degree center - 3)).sum) :=
  match surplusPairDecision ctx verified with
  | .pair value => value
  | .bounded small => by
      change (surplusPairInput ctx).items.values.length ≤ 1 at small
      have itemCountTwo : 2 ≤ (surplusPairInput ctx).items.values.length := by
        rwa [surplusPair_itemCount_eq_sigma ctx]
      omega

theorem surplusPairOfTwoLeSigma_distinct
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (verified : VerifiedSurplusPairPrefix ctx)
    (twoLe : 2 ≤
      (ctx.G.object.input.vertices.orderedValues.map
        (fun center => ctx.G.object.degree center - 3)).sum) :
    (surplusPairOfTwoLeSigma ctx verified twoLe).first ≠
      (surplusPairOfTwoLeSigma ctx verified twoLe).second :=
  (surplusPairOfTwoLeSigma ctx verified twoLe).distinct

theorem runSurplusPairCT9_checks_linear
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    (surplusPairInput ctx).items.values.length ≤
      (surplusPairInput ctx).items.values.length + 1 :=
  Graph.SurplusPortActivity.pairChecks_linear
    (fixedPackedInput ctx) ctx.G.object
    (packedStaticInput.fixedContext ctx).baseline
    ((fixedPackedInput ctx).dart_has_tight_endpoint
      (packedStaticInput.fixedContext ctx))

def verifiedSurplusPairPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedSparseSurplusPrefix ctx) :
    VerifiedSurplusPairPrefix ctx :=
  ⟨previous,
    Routes.CT6ToCT9.advance (surplusPairCapability ctx)
      (Graph.SurplusPortActivity.pairAdapter
        (fixedPackedInput ctx) ctx.G.object
        (packedStaticInput.fixedContext ctx).baseline
        ((fixedPackedInput ctx).dart_has_tight_endpoint
          (packedStaticInput.fixedContext ctx)))
      (surplusPairCurrent ctx previous)
      (sparseSurplusLedgerStage ctx previous)⟩

theorem exists_verifiedSurplusPairPrefix {V : Type u}
    (object : Object V) (baseline : Baseline object)
    (avoids : ¬Target object) :
    ∃ ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u},
      ∃ _ : VerifiedSurplusPairPrefix ctx,
        PackedProblem.{u}.rank ctx.G ≤
          PackedProblem.{u}.rank (Graph.PackedFiniteObject.pack object) := by
  obtain ⟨ctx, previous, rankLe⟩ :=
    exists_verifiedSparseSurplusPrefix object baseline avoids
  exact ⟨ctx, verifiedSurplusPairPrefix ctx previous, rankLe⟩

end Erdos64EG.Internal
