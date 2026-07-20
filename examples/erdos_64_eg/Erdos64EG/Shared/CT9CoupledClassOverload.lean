import Erdos64EG.Shared.CT9CapacityTokenLedger
import StructuralExhaustion.Graph.SurplusClasswiseOverload

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# CT9: coupled single-graph class overload

This block consumes the exact node-[136] complete-pair ledger.  For every
authored triple of homogeneous matching--star thresholds, CT9 either returns
one actual overloaded token--role fibre or certifies that the complete pair
count fits in the coupled capacity.  The overload token is then routed by its
literal sum constructor through the window/remainder/primitive decisions.
-/

noncomputable abbrev coupledClassActivationStage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  capacityTokenActivationStage ctx

noncomputable abbrev coupledClassProfile
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (windowSize remainderSize primitiveSize : Nat) :=
  Graph.SurplusClasswiseOverload.profile (coupledClassActivationStage ctx)
    windowSize remainderSize primitiveSize

noncomputable abbrev coupledClassItems
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  Graph.SurplusClasswiseOverload.items
    (setup := surplusPortActivationSetup ctx)

/-- Node `[137]`: the exact coupled excess is decided on the one selected
graph.  The positive result contains CT9's actual overloaded fibre; the
negative result contains the literal complete-pair capacity inequality. -/
noncomputable def coupledClassDecision
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (windowSize remainderSize primitiveSize : Nat) :=
  Graph.SurplusClasswiseOverload.decision (coupledClassActivationStage ctx)
    windowSize remainderSize primitiveSize

theorem coupledExcess_positive_iff
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (windowSize remainderSize primitiveSize : Nat) :
    0 < Graph.SurplusClasswiseOverload.coupledExcess
        (coupledClassActivationStage ctx)
        windowSize remainderSize primitiveSize ↔
      Graph.SurplusClasswiseOverload.coupledCapacity
          (coupledClassActivationStage ctx)
          windowSize remainderSize primitiveSize <
        (coupledClassItems ctx).values.length :=
  Graph.SurplusClasswiseOverload.coupledExcess_pos_iff
    (coupledClassActivationStage ctx) windowSize remainderSize primitiveSize

/-- Nodes `[139]` and `[141]`: an overloaded token follows exactly one of the
three manuscript class routes. -/
noncomputable def coupledOverloadClassRoute
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (windowSize remainderSize primitiveSize : Nat)
    (overload : (coupledClassProfile ctx windowSize remainderSize primitiveSize).Overload
      ctx.toBranchContext (coupledClassItems ctx)) :=
  Graph.SurplusClasswiseOverload.routedOverload
    (coupledClassActivationStage ctx) windowSize remainderSize primitiveSize
    overload

theorem coupledPairCount_eq_chooseSurplus
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    (Graph.SurplusCapacityTokenRouting.pairs
      (setup := surplusPortActivationSetup ctx)).card =
      Nat.choose (Graph.InducedPathWindowLedger.totalSurplus ctx.G.object) 2 := by
  calc
    (Graph.SurplusCapacityTokenRouting.pairs
        (setup := surplusPortActivationSetup ctx)).card =
        Nat.choose
          (Graph.SurplusPairResponse.slotEnumeration
            (setup := surplusPortActivationSetup ctx)).card 2 :=
      Core.Enumeration.orderedDistinctPairs_card _
    _ = Nat.choose
        (Graph.InducedPathWindowLedger.totalSurplus ctx.G.object) 2 := by
      rw [Graph.SurplusPortActivity.portSlots_card_eq_surplus]
      rfl

/-- The no-overload output bounds the literal complete pair count by the
coupled class capacity. -/
theorem withinCoupledCapacity_pairBound
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (windowSize remainderSize primitiveSize : Nat)
    (within : (coupledClassProfile ctx windowSize remainderSize primitiveSize).WithinCapacity
      (coupledClassItems ctx)) :
    (Graph.SurplusCapacityTokenRouting.pairs
      (setup := surplusPortActivationSetup ctx)).card ≤
      Graph.SurplusClasswiseOverload.maxCap
          windowSize remainderSize primitiveSize *
        ((Graph.SurplusCapacityTokenRouting.tokens
          (ctx := ctx) (setup := surplusPortActivationSetup ctx)).card * 25) := by
  have capacityBound := Graph.SurplusClasswiseOverload.totalCapacity_le
    (coupledClassActivationStage ctx) windowSize remainderSize primitiveSize
  have exactLength : (coupledClassItems ctx).values.length =
      (Graph.SurplusCapacityTokenRouting.pairs
        (setup := surplusPortActivationSetup ctx)).card := by
    exact Graph.SurplusClasswiseOverload.items_length
  calc
    (Graph.SurplusCapacityTokenRouting.pairs
        (setup := surplusPortActivationSetup ctx)).card =
        (coupledClassItems ctx).values.length := exactLength.symm
    _ ≤ (coupledClassProfile ctx windowSize remainderSize
        primitiveSize).totalCapacity := within.bounded
    _ = Graph.SurplusClasswiseOverload.coupledCapacity
        (coupledClassActivationStage ctx)
        windowSize remainderSize primitiveSize := rfl
    _ ≤ Graph.SurplusClasswiseOverload.maxCap
          windowSize remainderSize primitiveSize *
        ((Graph.SurplusCapacityTokenRouting.tokens
          (ctx := ctx) (setup := surplusPortActivationSetup ctx)).card * 25) :=
      capacityBound

/-- Node `[138]`: absence of coupled overload gives an explicit quadratic
surplus bound.  This is the finite, pointwise form of the near-cubic spine:
the square of the surplus is bounded by a fixed threshold coefficient times
the graph order. -/
theorem noCoupledOverload_quadraticSpine
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (windowSize remainderSize primitiveSize : Nat)
    (within : (coupledClassProfile ctx windowSize remainderSize primitiveSize).WithinCapacity
      (coupledClassItems ctx)) :
    (Graph.InducedPathWindowLedger.totalSurplus ctx.G.object) ^ 2 ≤
      (450 * Graph.SurplusClasswiseOverload.maxCap
          windowSize remainderSize primitiveSize + 1) *
        ctx.G.object.input.vertices.card := by
  let surplus := Graph.InducedPathWindowLedger.totalSurplus ctx.G.object
  let bound := Graph.SurplusClasswiseOverload.maxCap
    windowSize remainderSize primitiveSize
  have pairCapacity := withinCoupledCapacity_pairBound ctx
    windowSize remainderSize primitiveSize within
  rw [coupledPairCount_eq_chooseSurplus] at pairCapacity
  have tokenBound := capacityTokenSupply_le_nine_mul_vertices ctx
  have pairBound : Nat.choose surplus 2 ≤
      225 * bound * ctx.G.object.input.vertices.card := by
    calc
      Nat.choose surplus 2 ≤
          bound *
            ((Graph.SurplusCapacityTokenRouting.tokens
              (ctx := ctx) (setup := surplusPortActivationSetup ctx)).card * 25) :=
        pairCapacity
      _ ≤ bound * ((9 * ctx.G.object.input.vertices.card) * 25) :=
        Nat.mul_le_mul_left bound (Nat.mul_le_mul_right 25 tokenBound)
      _ = 225 * bound * ctx.G.object.input.vertices.card := by ring
  have surplusBound : surplus ≤ ctx.G.object.input.vertices.card :=
    totalSurplus_le_vertexCount ctx
  calc
    surplus ^ 2 = 2 * Nat.choose surplus 2 + surplus :=
      (Core.Enumeration.two_mul_choose_two_add surplus).symm
    _ ≤ 2 * (225 * bound * ctx.G.object.input.vertices.card) +
        ctx.G.object.input.vertices.card :=
      Nat.add_le_add (Nat.mul_le_mul_left 2 pairBound) surplusBound
    _ = (450 * bound + 1) * ctx.G.object.input.vertices.card := by ring

theorem coupledClassChecks_cubic
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (windowSize remainderSize primitiveSize : Nat) :
    Graph.SurplusClasswiseOverload.checks
      (setup := surplusPortActivationSetup ctx)
      windowSize remainderSize primitiveSize ≤
        225 * ctx.G.object.input.vertices.card ^ 3 := by
  unfold Graph.SurplusClasswiseOverload.checks
  have pairBound := capacityPairCount_le_square ctx
  have tokenBound := capacityTokenSupply_le_nine_mul_vertices ctx
  calc
    (Graph.SurplusCapacityTokenRouting.pairs
        (setup := surplusPortActivationSetup ctx)).card *
      ((Graph.SurplusCapacityTokenRouting.tokens
        (ctx := ctx) (setup := surplusPortActivationSetup ctx)).card * 25) ≤
      ctx.G.object.input.vertices.card ^ 2 *
        ((9 * ctx.G.object.input.vertices.card) * 25) :=
      Nat.mul_le_mul pairBound (Nat.mul_le_mul tokenBound (le_refl 25))
    _ = 225 * ctx.G.object.input.vertices.card ^ 3 := by ring

/-- Pointwise authored threshold triples.  The family is a dependent function;
the framework never enumerates this type. -/
abbrev CoupledClassThreshold := Nat × Nat × Nat

/-- Canonical pointwise CT9→CT9 profile for every authored threshold triple. -/
noncomputable def coupledClassPointwiseProfile
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedCapacityTokenPrefix ctx) :
    Routes.Accumulated.PointwiseAdapter .ct9 .ct9 CoupledClassThreshold
      (CapacityTokenLedger ctx previous.1) where
  Source := fun _threshold => CapacityTokenLedger ctx previous.1
  target := fun threshold =>
    (coupledClassProfile ctx threshold.1 threshold.2.1
      threshold.2.2).capability.executableInterface
  adapter := fun threshold => {
    targetContext := fun _source =>
      ((coupledClassProfile ctx threshold.1 threshold.2.1 threshold.2.2).input
        ctx.toBranchContext (coupledClassItems ctx)).context
    trigger := fun _source =>
      ⟨((coupledClassProfile ctx threshold.1 threshold.2.1 threshold.2.2).input
        ctx.toBranchContext (coupledClassItems ctx)).items⟩
  }
  current := fun _threshold => id

noncomputable def coupledClassTransitionStage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedCapacityTokenPrefix ctx) :=
  Routes.Accumulated.advancePointwise
    (coupledClassPointwiseProfile ctx previous)
    (capacityTokenLedgerStage ctx previous)

abbrev CoupledClassTransitionLedger
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedCapacityTokenPrefix ctx) :=
  Routes.Accumulated.PointwiseOutputLedger
    (coupledClassPointwiseProfile ctx previous)
    (capacityTokenLedgerStage ctx previous)

/-- Coupled-overload obligations accumulated on the literal pointwise CT9
execution. -/
structure CoupledClassOverloadFacts
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {previous : VerifiedCapacityTokenPrefix ctx}
    (_stage : CoupledClassTransitionLedger ctx previous) : Prop where
  stage : ∀ windowSize remainderSize primitiveSize, Nonempty (
    Graph.SurplusClasswiseOverload.VerifiedStage
      (coupledClassActivationStage ctx)
      windowSize remainderSize primitiveSize)
  exactPairCount :
    (Graph.SurplusCapacityTokenRouting.pairs
      (setup := surplusPortActivationSetup ctx)).card =
      Nat.choose (Graph.InducedPathWindowLedger.totalSurplus ctx.G.object) 2
  polynomial : ∀ windowSize remainderSize primitiveSize,
    Graph.SurplusClasswiseOverload.checks
      (setup := surplusPortActivationSetup ctx)
      windowSize remainderSize primitiveSize ≤
        225 * ctx.G.object.input.vertices.card ^ 3

abbrev CoupledClassOverloadLedger
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedCapacityTokenPrefix ctx) :=
  Core.Routing.LedgerExtension
    (CoupledClassTransitionLedger ctx previous)
    (CoupledClassOverloadFacts ctx)

/-- Verified prefix through the coupled CT9 decision and both token-class
tests. -/
abbrev VerifiedCoupledClassOverloadPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  Sigma fun previous : VerifiedCapacityTokenPrefix ctx =>
    Core.Routing.ResidualStage .ct9
      (CoupledClassOverloadLedger ctx previous)

noncomputable def verifiedCoupledClassOverloadPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedCapacityTokenPrefix ctx) :
    VerifiedCoupledClassOverloadPrefix ctx :=
  let stage := coupledClassTransitionStage ctx previous
  ⟨previous, stage.extend {
    stage := fun windowSize remainderSize primitiveSize => ⟨
      Graph.SurplusClasswiseOverload.verifiedStage
        (coupledClassActivationStage ctx)
        windowSize remainderSize primitiveSize⟩
    exactPairCount := coupledPairCount_eq_chooseSurplus ctx
    polynomial := coupledClassChecks_cubic ctx
  }⟩

/-- Canonical complete CT9 stage after the coupled overload decision. -/
noncomputable def coupledClassOverloadLedgerStage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (verified : VerifiedCoupledClassOverloadPrefix ctx) :=
  verified.2

theorem exists_verifiedCoupledClassOverloadPrefix {V : Type u}
    (object : Object V) (baseline : Baseline object)
    (avoids : ¬Target object) :
    ∃ ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u},
      ∃ _ : VerifiedCoupledClassOverloadPrefix.{u} ctx,
        PackedProblem.{u}.rank ctx.G ≤
          PackedProblem.{u}.rank (Graph.PackedFiniteObject.pack object) := by
  obtain ⟨ctx, previous, rankLe⟩ :=
    exists_verifiedCapacityTokenPrefix object baseline avoids
  exact ⟨ctx, verifiedCoupledClassOverloadPrefix ctx previous, rankLe⟩

end Erdos64EG.Internal
