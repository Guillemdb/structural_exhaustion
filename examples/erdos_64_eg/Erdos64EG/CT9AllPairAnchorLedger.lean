import Erdos64EG.CT15SparsePairResponses
import StructuralExhaustion.CT9.AnchoredPairLedger
import StructuralExhaustion.Graph.SurplusPairTokenRouting

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u v

/-!
# Exact CT9 anchor ledger for every surplus pair

This layer assigns every already scheduled pair from node `[130]` to its
canonical first surplus slot.  The resulting fibres are literal stars and
partition the whole pair schedule.
-/

noncomputable abbrev allPairSlotEnumeration
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  Graph.SurplusPairResponse.slotEnumeration
    (setup := surplusPortActivationSetup ctx)

noncomputable def allPairAnchorCapability
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  CT9.AnchoredPairLedger.capability PackedProblem.{u}
    (allPairSlotEnumeration ctx)

noncomputable def allPairAnchorInput
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  CT9.AnchoredPairLedger.input
    (P := PackedProblem.{u})
    (items := allPairSlotEnumeration ctx)
    (capacity := fun _ ↦ 0)
    ctx.toBranchContext

/-- Every scheduled pair from node `[130]` appears in exactly one anchor
fibre, independently of its free/blocked classification. -/
theorem allPairAnchor_noOvercounting
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    (Graph.SurplusPairResponse.pairEnumeration
      (setup := surplusPortActivationSetup ctx)).orderedValues.length =
      ((allPairSlotEnumeration ctx).orderedValues.map fun slot ↦
        CT9.fibreCount (allPairAnchorCapability ctx)
          (allPairAnchorInput ctx) slot).sum := by
  exact CT9.AnchoredPairLedger.noOvercounting
    (allPairSlotEnumeration ctx) ctx.toBranchContext

/-- The anchor-token supply is exactly the already verified surplus count. -/
theorem allPairAnchor_tokenSupply_eq_sigma
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    (allPairSlotEnumeration ctx).orderedValues.length =
      (ctx.G.object.input.vertices.orderedValues.map
        (fun center ↦ ctx.G.object.degree center - 3)).sum := by
  rw [FinEnum.orderedValues_length]
  exact Graph.SurplusPortActivity.portSlots_card_eq_surplus ctx.G.object

/-- Every CT9 fibre is a literal scheduled-pair star at its anchor slot. -/
theorem allPairAnchor_sameAnchor
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {slot : (allPairAnchorCapability ctx).Label}
    {left right : (allPairAnchorCapability ctx).Item}
    (leftMember : left ∈ CT9.fibre (allPairAnchorCapability ctx)
      (allPairAnchorInput ctx) slot)
    (rightMember : right ∈ CT9.fibre (allPairAnchorCapability ctx)
      (allPairAnchorInput ctx) slot) :
    CT9.AnchoredPairLedger.anchor left =
      CT9.AnchoredPairLedger.anchor right := by
  exact CT9.AnchoredPairLedger.same_anchor_of_mem_fibre
    ctx.toBranchContext leftMember rightMember

/-- The local pair enumeration remains quadratic in the exact surplus-slot
schedule, hence polynomial in the authored graph order. -/
theorem allPairAnchor_pairCount_le_square
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    (Graph.SurplusPairResponse.pairEnumeration
      (setup := surplusPortActivationSetup ctx)).card ≤
        (allPairSlotEnumeration ctx).card ^ 2 :=
  CT9.AnchoredPairLedger.pairCount_le_square (allPairSlotEnumeration ctx)

/-! ## Exact free/blocked routing into the non-near-cubic ledger -/

noncomputable abbrev allPairTokenRoutingStage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  sparsePairActivationStage ctx

noncomputable abbrev allPairTokenRoutingCapability
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  Graph.SurplusPairTokenRouting.capability (allPairTokenRoutingStage ctx)

noncomputable abbrev allPairTokenRoutingInput
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  Graph.SurplusPairTokenRouting.ct9Input (allPairTokenRoutingStage ctx)

/-- Complete reusable graph-level execution and routing certificate. -/
noncomputable abbrev allPairTokenRoutingVerifiedStage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  Graph.SurplusPairTokenRouting.verifiedStage
    (allPairTokenRoutingStage ctx)

theorem allPairTokenRouting_terminal
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    (Graph.SurplusPairTokenRouting.run
      (allPairTokenRoutingStage ctx)).terminal = .overloaded ∨
    (Graph.SurplusPairTokenRouting.run
      (allPairTokenRoutingStage ctx)).terminal = .bounded :=
  (allPairTokenRoutingVerifiedStage ctx).terminal

theorem allPairTokenRouting_verified
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    (Graph.SurplusPairTokenRouting.run
      (allPairTokenRoutingStage ctx)).outcome.Valid :=
  (allPairTokenRoutingVerifiedStage ctx).verified

theorem allPairTokenRouting_traceValid
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    CT9.Graph.ValidTrace (allPairTokenRoutingCapability ctx)
      (allPairTokenRoutingInput ctx)
      (Graph.SurplusPairTokenRouting.run
        (allPairTokenRoutingStage ctx)).trace :=
  (allPairTokenRoutingVerifiedStage ctx).traceValid

theorem allPairTokenRouting_total
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    ∃ result,
      result = Graph.SurplusPairTokenRouting.run
        (allPairTokenRoutingStage ctx) ∧
      result.outcome.Valid ∧
      CT9.Graph.ValidTrace (allPairTokenRoutingCapability ctx)
        (allPairTokenRoutingInput ctx) result.trace :=
  (allPairTokenRoutingVerifiedStage ctx).total

/-- CT9 accounts for every pair exactly once using the product of its first
selected surplus port and its exact five-way route role. -/
theorem allPairTokenRouting_noOvercounting
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    (allPairTokenRoutingInput ctx).items.values.length =
      ((allPairTokenRoutingCapability ctx).labels.orderedValues.map fun label ↦
        CT9.fibreCount (allPairTokenRoutingCapability ctx)
          (allPairTokenRoutingInput ctx) label).sum :=
  Graph.SurplusPairTokenRouting.noOvercounting
    (allPairTokenRoutingStage ctx)

/-- The fifth role is the literal negative branch of the admitted blocker scan. -/
theorem allPairTokenRouting_freeRole
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (pair : Graph.SurplusPairResponse.FreePair
      (allPairTokenRoutingStage ctx)) :
    Graph.SurplusPairTokenRouting.pairRole
      (allPairTokenRoutingStage ctx) pair.1 =
        .freeAnchor :=
  Graph.SurplusPairTokenRouting.free_role
    (allPairTokenRoutingStage ctx) pair

/-- The positive blocker branch keeps the canonical first blocker kind and
does not manufacture a capacity-token subtype before node `[134]`. -/
theorem allPairTokenRouting_blockedRole
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (pair : Graph.SurplusPairResponse.BlockedPair
      (allPairTokenRoutingStage ctx)) :
    Graph.SurplusPairTokenRouting.pairRole
      (allPairTokenRoutingStage ctx) pair.1 =
        .blocked (Graph.SurplusTokenRole.admittedKind
          (Graph.SurplusPairResponse.canonicalBlocker
            (allPairTokenRoutingStage ctx) pair).value) :=
  Graph.SurplusPairTokenRouting.blocked_role
    (allPairTokenRoutingStage ctx) pair

/-- A free-anchor CT9 fibre is the exact primitive selected-port handoff:
every member is blocker-free and has the displayed token as first port. -/
theorem allPairTokenRouting_freeHandoff
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {token : Graph.SurplusPairTokenRouting.Token
      (setup := surplusPortActivationSetup ctx)}
    (item : Graph.SurplusPairTokenRouting.FreeAnchorMember
      (allPairTokenRoutingStage ctx) token) :
    ¬(Graph.SurplusPairResponse.blockerFamily
        (allPairTokenRoutingStage ctx)).HasBlocker item.pair ∧
      item.pair.first = token :=
  ⟨Graph.SurplusPairTokenRouting.freeAnchorFibre_member_is_free
      (allPairTokenRoutingStage ctx) item,
    Graph.SurplusPairTokenRouting.freeAnchorFibre_member_first
      (allPairTokenRoutingStage ctx) item⟩

/-- The blocked handoff contains the full first-hit proof expected by the
canonical blocker ledger, including all earlier failed candidates. -/
theorem allPairTokenRouting_blockedHandoff
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (pair : Graph.SurplusPairResponse.BlockedPair
      (allPairTokenRoutingStage ctx)) :
    (Graph.SurplusPairResponse.canonicalBlocker
        (allPairTokenRoutingStage ctx) pair).value ∈
      ((Graph.SurplusPairResponse.localBlockerProfile
        (allPairTokenRoutingStage ctx)).candidates pair.1).values ∧
    (Graph.SurplusPairResponse.localBlockerProfile
        (allPairTokenRoutingStage ctx)).Blocks pair.1
      (Graph.SurplusPairResponse.canonicalBlocker
        (allPairTokenRoutingStage ctx) pair).value ∧
    ∀ candidate ∈ (Graph.SurplusPairResponse.canonicalBlocker
        (allPairTokenRoutingStage ctx) pair).before,
      ¬(Graph.SurplusPairResponse.localBlockerProfile
        (allPairTokenRoutingStage ctx)).Blocks pair.1 candidate :=
  Graph.SurplusPairTokenRouting.blocked_retains_canonical_blocker
    (allPairTokenRoutingStage ctx) pair

/-- The total route has a fixed five-role alphabet and one product-label
check for each pair, token, and role. -/
theorem allPairTokenRouting_checks
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Graph.SurplusPairTokenRouting.checks (allPairTokenRoutingStage ctx) =
      (Graph.SurplusPairResponse.pairEnumeration
        (setup := surplusPortActivationSetup ctx)).card *
        ((allPairSlotEnumeration ctx).card * 5) :=
  Graph.SurplusPairTokenRouting.checks_eq (allPairTokenRoutingStage ctx)

/-- Complete CT9 product work is bounded by `5 n⁶`. -/
theorem allPairTokenRouting_checks_polynomial
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Graph.SurplusPairTokenRouting.checks (allPairTokenRoutingStage ctx) ≤
      5 * ctx.G.object.input.vertices.card ^ 6 :=
  Graph.SurplusPairTokenRouting.checks_le_five_mul_sixthPower
    (allPairTokenRoutingStage ctx)

/-- The sparse-envelope residual sharpens the selected-port schedule from the
generic quadratic supply to at most `n`. -/
theorem allPairTokenRouting_tokenCount_le_vertexCount
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    (allPairSlotEnumeration ctx).card ≤
      ctx.G.object.input.vertices.card := by
  have slotsEq : (allPairSlotEnumeration ctx).card =
      (ctx.G.object.input.vertices.orderedValues.map
        (fun center ↦ ctx.G.object.degree center - 3)).sum := by
    simpa only [FinEnum.orderedValues_length] using
      (allPairAnchor_tokenSupply_eq_sigma ctx)
  have ledgerEq := Graph.SurplusPortActivity.degreeExcess_sum_int_eq
    ctx.G.object 3 (fun vertex ↦
      (packedStaticInput.fixedContext ctx).baseline.trans
        (ctx.G.object.minDegree_le_degree vertex))
  have edgeBound := sparseEnvelope_edgeBound ctx
  have countLarge := sparseEnvelope_vertexCount_gt_three ctx
  rw [slotsEq]
  omega

/-- On the actual sparse residual the CT9 product audit is cubic, not merely
the generic sixth-power worst case. -/
theorem allPairTokenRouting_checks_cubic
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Graph.SurplusPairTokenRouting.checks (allPairTokenRoutingStage ctx) ≤
      5 * ctx.G.object.input.vertices.card ^ 3 :=
  Graph.SurplusPairTokenRouting.checks_le_five_mul_cube_of_token_card_le
    (allPairTokenRoutingStage ctx) ctx.G.object.input.vertices.card
    (allPairTokenRouting_tokenCount_le_vertexCount ctx)

/-- Mathematical adapter for the canonical CT15→CT9 all-pair routing edge. -/
noncomputable def allPairTokenRoutingAdapter
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {Source : Sort v} :
    Routes.Accumulated.Adapter Source
      (allPairTokenRoutingCapability ctx).executableInterface where
  targetContext := fun _source => (allPairTokenRoutingInput ctx).context
  trigger := fun _source => ⟨(allPairTokenRoutingInput ctx).items⟩

/-- Framework-owned CT15→CT9 execution retaining the full pair-response
ledger. -/
noncomputable def allPairTokenRoutingTransitionStage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedSparsePairResponsePrefix ctx) :=
  Routes.Accumulated.advanceCurrent
    (allPairTokenRoutingCapability ctx).executableInterface
    (allPairTokenRoutingAdapter (Source := SparsePairResponseLedger ctx previous.1) ctx)
    (sparsePairResponseLedgerStage ctx previous)

abbrev AllPairTokenRoutingTransitionLedger
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedSparsePairResponsePrefix ctx) :=
  Routes.Accumulated.OutputLedger (sourceTactic := .ct15)
    (allPairTokenRoutingCapability ctx).executableInterface
    (allPairTokenRoutingAdapter (Source := SparsePairResponseLedger ctx previous.1)
      ctx) (sparsePairResponseLedgerStage ctx previous)

/-- Node `[131]` facts attached to the exact CT9 execution. -/
structure AllPairTokenRoutingFacts
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    {previous : VerifiedSparsePairResponsePrefix ctx}
    (_stage : AllPairTokenRoutingTransitionLedger ctx previous) : Prop where
  routing : Graph.SurplusPairTokenRouting.VerifiedStage
    (allPairTokenRoutingStage ctx)
  localPolynomialChecks :
    Graph.SurplusPairTokenRouting.checks (allPairTokenRoutingStage ctx) ≤
      5 * ctx.G.object.input.vertices.card ^ 3
  polynomialPairs :
    (Graph.SurplusPairResponse.pairEnumeration
        (setup := surplusPortActivationSetup ctx)).card ≤
      ctx.G.object.input.vertices.card ^ 4

abbrev AllPairTokenRoutingLedger
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedSparsePairResponsePrefix ctx) :=
  Core.Routing.LedgerExtension
    (AllPairTokenRoutingTransitionLedger ctx previous)
    (AllPairTokenRoutingFacts ctx)

/-- Verified proof prefix through the repaired node `[131]` routing block. -/
abbrev VerifiedAllPairTokenRoutingPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  Sigma fun previous : VerifiedSparsePairResponsePrefix ctx =>
    Core.Routing.ResidualStage .ct9
      (AllPairTokenRoutingLedger ctx previous)

noncomputable def verifiedAllPairTokenRoutingPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedSparsePairResponsePrefix ctx) :
    VerifiedAllPairTokenRoutingPrefix ctx :=
  let stage := allPairTokenRoutingTransitionStage ctx previous
  ⟨previous, stage.extend {
    routing := allPairTokenRoutingVerifiedStage ctx
    localPolynomialChecks := allPairTokenRouting_checks_cubic ctx
    polynomialPairs := previous.2.output.added.polynomialPairs
  }⟩

/-- Canonical complete CT9 stage after node `[131]`. -/
noncomputable def allPairTokenRoutingLedgerStage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (verified : VerifiedAllPairTokenRoutingPrefix ctx) :=
  verified.2

theorem exists_verifiedAllPairTokenRoutingPrefix {V : Type u}
    (object : Object V) (baseline : Baseline object)
    (avoids : ¬Target object) :
    ∃ ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u},
      ∃ _ : VerifiedAllPairTokenRoutingPrefix.{u} ctx,
        PackedProblem.{u}.rank ctx.G ≤
          PackedProblem.{u}.rank (Graph.PackedFiniteObject.pack object) := by
  obtain ⟨ctx, previous, rankLe⟩ :=
    exists_verifiedSparsePairResponsePrefix object baseline avoids
  exact ⟨ctx, verifiedAllPairTokenRoutingPrefix ctx previous, rankLe⟩

end Erdos64EG.Internal
