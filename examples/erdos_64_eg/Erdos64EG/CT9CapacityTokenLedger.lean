import Erdos64EG.CT9AllPairAnchorLedger
import StructuralExhaustion.Graph.SurplusCapacityTokenRouting

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u v

/-!
# CT9: canonical capacity tokens and the complete 25-role ledger

This block consumes the exact free/blocked output of nodes `[130]`--`[132]`.
Raw quotient-audit kinds leave at `[133]`; every admitted blocked pair receives
the manuscript's deterministic capacity token at `[134]`; the selected CT12
packing supplies the exact window-incidence identity at `[135]`; and CT9
partitions the complete pair schedule into the 25 actual token--role fibres at
`[136]`.
-/

noncomputable abbrev capacityTokenActivationStage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  allPairTokenRoutingStage ctx

noncomputable abbrev capacityTokenRoutingStage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  Graph.SurplusCapacityTokenRouting.verifiedStage
    (capacityTokenActivationStage ctx)

private theorem cubicBaseline
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    ∀ vertex, 3 ≤ ctx.G.object.degree vertex := by
  intro vertex
  exact (packedStaticInput.fixedContext ctx).baseline.trans
    (ctx.G.object.minDegree_le_degree vertex)

/-- Node `[133]` is a proved exit, not an assumed restriction: neither raw
quotient-audit kind can be emitted by the admitted local candidate scan. -/
theorem sparsePairAuditExit_closed
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (pair : Graph.SurplusPairResponse.BlockedPair
      (capacityTokenActivationStage ctx)) :
    let candidate := (Graph.SurplusPairResponse.canonicalBlocker
      (capacityTokenActivationStage ctx) pair).value
    candidate.kind ≠ .profile ∧ candidate.kind ≠ .target := by
  exact Graph.SurplusPairBlocker.Pair.candidate_kind_ne_profile_target _

/-- Node `[134]`: every blocked scheduled pair is assigned exactly one value
of the disjoint capacity-token universe by the canonical priority map. -/
theorem canonicalBlockedToken_total
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (pair : Graph.SurplusPairResponse.BlockedPair
      (capacityTokenActivationStage ctx)) :
    Graph.SurplusCapacityTokenRouting.pairToken
        (capacityTokenActivationStage ctx) pair.1 =
      Graph.SurplusCapacityTokenRouting.blockedToken
        (capacityTokenActivationStage ctx) pair :=
  Graph.SurplusCapacityTokenRouting.blocked_token
    (capacityTokenActivationStage ctx) pair

/-- Node `[135]`: actual outgoing incidences of the selected induced-`P₁₃`
windows have the exact manuscript supply `15 p₁₃ + σ_W`. -/
theorem exactWindowJoinIdentity
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    (Graph.InducedPathWindowLedger.tokens ctx.G.object).card =
      15 * p13 ctx +
        Graph.InducedPathWindowLedger.windowSurplus ctx.G.object := by
  rw [p13, ← Graph.InducedPathWindowLedger.packingNumber_eq_inducedPathPacking]
  exact
    Graph.InducedPathWindowLedger.tokens_card_eq_fifteen_mul_packing_add_surplus
      ctx.G.object (cubicBaseline ctx)

/-- The window ledger touches only selected windows, their thirteen fixed
positions, and the declared vertex schedule. -/
theorem windowJoinChecks_quadratic
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Graph.InducedPathWindowLedger.checks ctx.G.object ≤
      13 * ctx.G.object.input.vertices.card ^ 2 :=
  Graph.InducedPathWindowLedger.checks_le_thirteen_mul_square ctx.G.object

/-- Exact three-class token supply, before algebraic simplification. -/
theorem capacityTokenSupply_partition
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    (Graph.SurplusCapacityTokenRouting.tokens
      (ctx := ctx) (setup := surplusPortActivationSetup ctx)).card =
      (Graph.InducedPathWindowLedger.tokens ctx.G.object).card +
      (Graph.SurplusCapacityTokenRouting.remainderTokens (ctx := ctx)).card +
      (Graph.SurplusCapacityTokenRouting.primitiveTokens
        (ctx := ctx) (setup := surplusPortActivationSetup ctx)).card :=
  Graph.SurplusCapacityTokenRouting.token_supply_exact

/-- Exact simplified capacity supply from the manuscript.  The first
parenthesis is `|U_sp|`; the last surplus is the combined `σ_W+σ_R`. -/
theorem capacityTokenSupply_exact
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    (Graph.SurplusCapacityTokenRouting.tokens
      (ctx := ctx) (setup := surplusPortActivationSetup ctx)).card =
      (ctx.G.object.input.vertices.card + 2 * ctx.G.object.edgeCount +
        Graph.InducedPathWindowLedger.totalSurplus ctx.G.object) +
      15 * p13 ctx +
        Graph.InducedPathWindowLedger.totalSurplus ctx.G.object := by
  rw [p13, ← Graph.InducedPathWindowLedger.packingNumber_eq_inducedPathPacking]
  exact Graph.SurplusCapacityTokenRouting.token_supply_exact_simplified
    (cubicBaseline ctx)

theorem totalSurplus_handshake
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Graph.InducedPathWindowLedger.totalSurplus ctx.G.object +
        3 * ctx.G.object.input.vertices.card =
      2 * ctx.G.object.edgeCount := by
  exact Graph.SurplusPortActivity.degreeExcess_sum_add_baseline
    ctx.G.object 3 (cubicBaseline ctx)

theorem totalSurplus_le_vertexCount
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Graph.InducedPathWindowLedger.totalSurplus ctx.G.object ≤
      ctx.G.object.input.vertices.card := by
  have handshake := totalSurplus_handshake ctx
  have edgeBound := sparseEnvelope_edgeBound ctx
  have countLarge := sparseEnvelope_vertexCount_gt_three ctx
  omega

/-- Primitive vertices, edge incidences, and selected ports have the exact
linear sparse supply `≤ 6n`. -/
theorem primitiveTokenSupply_le_six_mul_vertices
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    (Graph.SurplusCapacityTokenRouting.primitiveTokens
      (ctx := ctx) (setup := surplusPortActivationSetup ctx)).card ≤
        6 * ctx.G.object.input.vertices.card := by
  rw [Graph.SurplusCapacityTokenRouting.primitive_card_eq_vertex_edges_surplus]
  have edgeBound := sparseEnvelope_edgeBound ctx
  have surplusBound := totalSurplus_le_vertexCount ctx
  omega

/-- Manuscript capacity bound `|T_cap| ≤ 8n+σ`. -/
theorem capacityTokenSupply_le_eight_mul_vertices_add_surplus
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    (Graph.SurplusCapacityTokenRouting.tokens
      (ctx := ctx) (setup := surplusPortActivationSetup ctx)).card ≤
      8 * ctx.G.object.input.vertices.card +
        Graph.InducedPathWindowLedger.totalSurplus ctx.G.object := by
  rw [capacityTokenSupply_exact]
  have primitiveBound := primitiveTokenSupply_le_six_mul_vertices ctx
  rw [Graph.SurplusCapacityTokenRouting.primitive_card_eq_vertex_edges_surplus]
    at primitiveBound
  have packed := thirteen_mul_p13_le_vertexCount ctx
  omega

theorem capacityTokenSupply_le_nine_mul_vertices
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    (Graph.SurplusCapacityTokenRouting.tokens
      (ctx := ctx) (setup := surplusPortActivationSetup ctx)).card ≤
      9 * ctx.G.object.input.vertices.card := by
  exact (capacityTokenSupply_le_eight_mul_vertices_add_surplus ctx).trans
    (by have := totalSurplus_le_vertexCount ctx; omega)

/-! The original node `[136]` consumes only the admitted blocked branch.
The complete 25-role ledger below is an additional exact refinement, not a
replacement for this predecessor-indexed execution. -/

/-- Original node `[136]`: the actual blocked-pair subtype is partitioned
exactly once by its canonical capacity token and its 24 realizable admitted
roles.  The manuscript's larger 36-role display is the same identity padded
by the twelve impossible profile/target audit rows. -/
theorem blockedCapacityLedger_noOvercounting
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    (Graph.SurplusCapacityTokenRouting.blockedInput
      (capacityTokenActivationStage ctx)).items.values.length =
      ((Graph.SurplusCapacityTokenRouting.blockedCapability
        (capacityTokenActivationStage ctx)).labels.orderedValues.map
        fun labelValue => CT9.fibreCount
          (Graph.SurplusCapacityTokenRouting.blockedCapability
            (capacityTokenActivationStage ctx))
          (Graph.SurplusCapacityTokenRouting.blockedInput
            (capacityTokenActivationStage ctx)) labelValue).sum :=
  Graph.SurplusCapacityTokenRouting.blocked_noOvercounting
    (capacityTokenActivationStage ctx)

theorem blockedCapacityRoleCount
    (_ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Graph.SurplusTokenRole.admittedRoleEnum.card = 24 :=
  Graph.SurplusTokenRole.admittedRole_card

/-- Literal original 36-row version of node `[136]`.  The profile/target
audit rows are present in the finite label table and empty because node
`[133]` has already excluded them. -/
theorem blockedFullCapacityLedger_noOvercounting
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    (Graph.SurplusCapacityTokenRouting.blockedFullInput
      (capacityTokenActivationStage ctx)).items.values.length =
      ((Graph.SurplusCapacityTokenRouting.blockedFullCapability
        (capacityTokenActivationStage ctx)).labels.orderedValues.map
        fun labelValue => CT9.fibreCount
          (Graph.SurplusCapacityTokenRouting.blockedFullCapability
            (capacityTokenActivationStage ctx))
          (Graph.SurplusCapacityTokenRouting.blockedFullInput
            (capacityTokenActivationStage ctx)) labelValue).sum :=
  Graph.SurplusCapacityTokenRouting.blockedFull_noOvercounting
    (capacityTokenActivationStage ctx)

theorem blockedFullCapacityRoleCount
    (_ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Graph.SurplusTokenRole.roleEnum.card = 36 :=
  Graph.SurplusTokenRole.role_card

theorem blockedCapacityLedgerChecks
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Graph.SurplusCapacityTokenRouting.blockedChecks
        (capacityTokenActivationStage ctx) =
      (Graph.SurplusCapacityTokenRouting.blockedPairs
        (capacityTokenActivationStage ctx)).card *
        ((Graph.SurplusCapacityTokenRouting.tokens
          (ctx := ctx) (setup := surplusPortActivationSetup ctx)).card * 24) :=
  Graph.SurplusCapacityTokenRouting.blockedChecks_eq
    (capacityTokenActivationStage ctx)

/-- Node `[136]`: all scheduled pairs occur in exactly one of the 25 actual
capacity-token/role fibres. -/
theorem totalCapacityLedger_noOvercounting
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    (Graph.SurplusCapacityTokenRouting.ct9Input
      (capacityTokenActivationStage ctx)).items.values.length =
      ((Graph.SurplusCapacityTokenRouting.capability
        (capacityTokenActivationStage ctx)).labels.orderedValues.map
        fun labelValue => CT9.fibreCount
          (Graph.SurplusCapacityTokenRouting.capability
            (capacityTokenActivationStage ctx))
          (Graph.SurplusCapacityTokenRouting.ct9Input
            (capacityTokenActivationStage ctx)) labelValue).sum :=
  Graph.SurplusCapacityTokenRouting.noOvercounting
    (capacityTokenActivationStage ctx)

theorem totalCapacityRoleCount
    (_ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Graph.SurplusTokenRole.totalRoleEnum.card = 25 :=
  Graph.SurplusTokenRole.totalRole_card

theorem capacityPairCount_le_square
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    (Graph.SurplusPairResponse.pairEnumeration
      (setup := surplusPortActivationSetup ctx)).card ≤
      ctx.G.object.input.vertices.card ^ 2 := by
  have pairSlots := Core.Enumeration.orderedDistinctPairs_card_le_square
    (allPairSlotEnumeration ctx)
  have slotBound := allPairTokenRouting_tokenCount_le_vertexCount ctx
  exact pairSlots.trans (Nat.pow_le_pow_left slotBound 2)

/-- The complete 25-role audit remains cubic: no graph family, path family,
or recursively generated universe is materialized. -/
theorem capacityLedgerChecks_cubic
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Graph.SurplusCapacityTokenRouting.checks
      (capacityTokenActivationStage ctx) ≤
        225 * ctx.G.object.input.vertices.card ^ 3 := by
  rw [Graph.SurplusCapacityTokenRouting.checks_eq]
  have pairBound := capacityPairCount_le_square ctx
  have tokenBound := capacityTokenSupply_le_nine_mul_vertices ctx
  calc
    (Graph.SurplusPairResponse.pairEnumeration
        (setup := surplusPortActivationSetup ctx)).card *
      ((Graph.SurplusCapacityTokenRouting.tokens
        (ctx := ctx) (setup := surplusPortActivationSetup ctx)).card * 25) ≤
      ctx.G.object.input.vertices.card ^ 2 *
        ((9 * ctx.G.object.input.vertices.card) * 25) :=
      Nat.mul_le_mul pairBound (Nat.mul_le_mul tokenBound (le_refl 25))
    _ = 225 * ctx.G.object.input.vertices.card ^ 3 := by ring

/-- Mathematical adapter for the canonical CT9→CT9 capacity-token
refinement. -/
noncomputable def capacityTokenAdapter
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {Source : Sort v} :
    Routes.Accumulated.Adapter Source
      (Graph.SurplusCapacityTokenRouting.capability
        (capacityTokenActivationStage ctx)).executableInterface where
  targetContext := fun _source =>
    (Graph.SurplusCapacityTokenRouting.ct9Input
      (capacityTokenActivationStage ctx)).context
  trigger := fun _source =>
    ⟨(Graph.SurplusCapacityTokenRouting.ct9Input
      (capacityTokenActivationStage ctx)).items⟩

noncomputable def capacityTokenTransitionStage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedAllPairTokenRoutingPrefix ctx) :=
  Routes.Accumulated.advanceCurrent
    (Graph.SurplusCapacityTokenRouting.capability
      (capacityTokenActivationStage ctx)).executableInterface
    (capacityTokenAdapter
      (Source := AllPairTokenRoutingLedger ctx previous.1) ctx)
    (allPairTokenRoutingLedgerStage ctx previous)

abbrev CapacityTokenTransitionLedger
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedAllPairTokenRoutingPrefix ctx) :=
  Routes.Accumulated.OutputLedger (sourceTactic := .ct9)
    (Graph.SurplusCapacityTokenRouting.capability
      (capacityTokenActivationStage ctx)).executableInterface
    (capacityTokenAdapter
      (Source := AllPairTokenRoutingLedger ctx previous.1) ctx)
    (allPairTokenRoutingLedgerStage ctx previous)

/-- Mathematical obligations of nodes `[133]`--`[136]`, accumulated on the
literal refined CT9 execution. -/
structure CapacityTokenFacts
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {previous : VerifiedAllPairTokenRoutingPrefix ctx}
    (_stage : CapacityTokenTransitionLedger ctx previous) : Prop where
  routing : Graph.SurplusCapacityTokenRouting.VerifiedStage
    (capacityTokenActivationStage ctx)
  auditExit : ∀ pair : Graph.SurplusPairResponse.BlockedPair
      (capacityTokenActivationStage ctx),
    let candidate := (Graph.SurplusPairResponse.canonicalBlocker
      (capacityTokenActivationStage ctx) pair).value
    candidate.kind ≠ .profile ∧ candidate.kind ≠ .target
  windowJoin : (Graph.InducedPathWindowLedger.tokens ctx.G.object).card =
    15 * p13 ctx + Graph.InducedPathWindowLedger.windowSurplus ctx.G.object
  exactSupply :
    (Graph.SurplusCapacityTokenRouting.tokens
      (ctx := ctx) (setup := surplusPortActivationSetup ctx)).card =
      (ctx.G.object.input.vertices.card + 2 * ctx.G.object.edgeCount +
        Graph.InducedPathWindowLedger.totalSurplus ctx.G.object) +
      15 * p13 ctx + Graph.InducedPathWindowLedger.totalSurplus ctx.G.object
  blockedRouting : CT9.TokenRoleLedger.VerifiedStage
    (Graph.SurplusCapacityTokenRouting.tokens
      (ctx := ctx) (setup := surplusPortActivationSetup ctx))
    Graph.SurplusTokenRole.admittedRoleEnum
    (Graph.SurplusCapacityTokenRouting.blockedToken
      (capacityTokenActivationStage ctx))
    (Graph.SurplusCapacityTokenRouting.blockedRole
      (capacityTokenActivationStage ctx))
    ctx.toBranchContext
    (Graph.SurplusCapacityTokenRouting.blockedPairs
      (capacityTokenActivationStage ctx)).toOrderedCollection
  blockedLedger :
    (Graph.SurplusCapacityTokenRouting.blockedInput
      (capacityTokenActivationStage ctx)).items.values.length =
      ((Graph.SurplusCapacityTokenRouting.blockedCapability
        (capacityTokenActivationStage ctx)).labels.orderedValues.map
        fun labelValue => CT9.fibreCount
          (Graph.SurplusCapacityTokenRouting.blockedCapability
            (capacityTokenActivationStage ctx))
          (Graph.SurplusCapacityTokenRouting.blockedInput
            (capacityTokenActivationStage ctx)) labelValue).sum
  blockedRoleCount : Graph.SurplusTokenRole.admittedRoleEnum.card = 24
  blockedFullRouting : CT9.TokenRoleLedger.VerifiedStage
    (Graph.SurplusCapacityTokenRouting.tokens
      (ctx := ctx) (setup := surplusPortActivationSetup ctx))
    Graph.SurplusTokenRole.roleEnum
    (Graph.SurplusCapacityTokenRouting.blockedToken
      (capacityTokenActivationStage ctx))
    (Graph.SurplusCapacityTokenRouting.blockedFullRole
      (capacityTokenActivationStage ctx))
    ctx.toBranchContext
    (Graph.SurplusCapacityTokenRouting.blockedPairs
      (capacityTokenActivationStage ctx)).toOrderedCollection
  blockedFullLedger :
    (Graph.SurplusCapacityTokenRouting.blockedFullInput
      (capacityTokenActivationStage ctx)).items.values.length =
      ((Graph.SurplusCapacityTokenRouting.blockedFullCapability
        (capacityTokenActivationStage ctx)).labels.orderedValues.map
        fun labelValue => CT9.fibreCount
          (Graph.SurplusCapacityTokenRouting.blockedFullCapability
            (capacityTokenActivationStage ctx))
          (Graph.SurplusCapacityTokenRouting.blockedFullInput
            (capacityTokenActivationStage ctx)) labelValue).sum
  blockedFullRoleCount : Graph.SurplusTokenRole.roleEnum.card = 36
  exactLedger :
    (Graph.SurplusCapacityTokenRouting.ct9Input
      (capacityTokenActivationStage ctx)).items.values.length =
      ((Graph.SurplusCapacityTokenRouting.capability
        (capacityTokenActivationStage ctx)).labels.orderedValues.map
        fun labelValue => CT9.fibreCount
          (Graph.SurplusCapacityTokenRouting.capability
            (capacityTokenActivationStage ctx))
          (Graph.SurplusCapacityTokenRouting.ct9Input
            (capacityTokenActivationStage ctx)) labelValue).sum
  roleCount : Graph.SurplusTokenRole.totalRoleEnum.card = 25
  windowChecks : Graph.InducedPathWindowLedger.checks ctx.G.object ≤
    13 * ctx.G.object.input.vertices.card ^ 2
  ledgerChecks : Graph.SurplusCapacityTokenRouting.checks
    (capacityTokenActivationStage ctx) ≤
      225 * ctx.G.object.input.vertices.card ^ 3

abbrev CapacityTokenLedger
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedAllPairTokenRoutingPrefix ctx) :=
  Core.Routing.LedgerExtension
    (CapacityTokenTransitionLedger ctx previous)
    (CapacityTokenFacts ctx)

/-- Verified prefix through the whole nodes `[133]`--`[136]` CT block. -/
abbrev VerifiedCapacityTokenPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  Sigma (CapacityTokenLedger ctx)

noncomputable def verifiedCapacityTokenPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedAllPairTokenRoutingPrefix ctx) :
    VerifiedCapacityTokenPrefix ctx :=
  let stage := capacityTokenTransitionStage ctx previous
  ⟨previous, ⟨stage, {
    routing := capacityTokenRoutingStage ctx
    auditExit := sparsePairAuditExit_closed ctx
    windowJoin := exactWindowJoinIdentity ctx
    exactSupply := capacityTokenSupply_exact ctx
    blockedRouting := Graph.SurplusCapacityTokenRouting.blockedVerifiedStage
      (capacityTokenActivationStage ctx)
    blockedLedger := blockedCapacityLedger_noOvercounting ctx
    blockedRoleCount := blockedCapacityRoleCount ctx
    blockedFullRouting := Graph.SurplusCapacityTokenRouting.blockedFullVerifiedStage
      (capacityTokenActivationStage ctx)
    blockedFullLedger := blockedFullCapacityLedger_noOvercounting ctx
    blockedFullRoleCount := blockedFullCapacityRoleCount ctx
    exactLedger := totalCapacityLedger_noOvercounting ctx
    roleCount := totalCapacityRoleCount ctx
    windowChecks := windowJoinChecks_quadratic ctx
    ledgerChecks := capacityLedgerChecks_cubic ctx
  }⟩⟩

/-- Canonical complete CT9 stage after node `[136]`. -/
noncomputable def capacityTokenLedgerStage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (verified : VerifiedCapacityTokenPrefix ctx) :=
  verified.2.previous.ledgerStage.extend verified.2.added

theorem exists_verifiedCapacityTokenPrefix {V : Type u}
    (object : Object V) (baseline : Baseline object)
    (avoids : ¬Target object) :
    ∃ ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u},
      ∃ _ : VerifiedCapacityTokenPrefix.{u} ctx,
        PackedProblem.{u}.rank ctx.G ≤
          PackedProblem.{u}.rank (Graph.PackedFiniteObject.pack object) := by
  obtain ⟨ctx, previous, rankLe⟩ :=
    exists_verifiedAllPairTokenRoutingPrefix object baseline avoids
  exact ⟨ctx, verifiedCapacityTokenPrefix ctx previous, rankLe⟩

end Erdos64EG.Internal
