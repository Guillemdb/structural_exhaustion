import Erdos64EG.Node48
import Erdos64EG.Shared.P13SequentialWindowLedger
import StructuralExhaustion.Core.FiniteTypeEntropy

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Diagram node [49]: entropy of realized remainder states

The state family is the image of the current residual's compatible global
completions under restriction to the exact remainder carried by node [31].  It is not an
ambient family of all graphs satisfying necessary constraints.  Core's
sequential ledger owns every hot/cold decision and aggregate transition.
-/

/-- The realized remainder family and every retained hot-window choice are
recoverable from one common compatible completion.  The generic framework
owns the resulting product-capacity theorem; this profile supplies only the
Problem-64 restriction map and the aggregate's graph-semantic reglue laws. -/
noncomputable def node49RealizedRemainderHotCapacityProfile
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {rate : P13BarrierRateCertificate}
    (aggregate : P13SequentialHotAggregate ctx rate) :
    Core.DependentOwnerGlueCapacity.BaseProfile where
  Base := Core.DependentOwnerGlueCapacity.RealizedProjection
    aggregate.JointState
    (SimpleGraph (P13RemainderVertex ctx)) aggregate.remainderGraph
  finiteBase := inferInstance
  Owner := Fin aggregate.retained.length
  owners := inferInstance
  Local := P13RetainedLocalChoice aggregate.retained
  locals := aggregate.localChoices
  Global := aggregate.JointState
  Code := aggregate.Code
  codes := aggregate.codes
  glue := fun base choice =>
    aggregate.reglue (Classical.choose base.property) choice
  recoverBase := fun joint =>
    Core.DependentOwnerGlueCapacity.realizedProjectionValue
      aggregate.remainderGraph joint
  recoverLocal := aggregate.recover
  recoverBase_glue := by
    intro base choice
    apply Subtype.ext
    change aggregate.remainderGraph
        (aggregate.reglue (Classical.choose base.property) choice) = base.1
    rw [aggregate.remainderGraph_reglue]
    exact Classical.choose_spec base.property
  recoverLocal_glue := by
    intro base choice owner
    exact aggregate.recover_reglue
      (Classical.choose base.property) choice owner
  code := aggregate.skeletonCode
  codeInjectiveOnGlue := by
    intro leftBase rightBase leftChoice rightChoice equal
    exact aggregate.skeletonCodeInjective equal

/-- Exact same-skeleton joint capacity required before node [52] may add the
remainder and hot-window entropy contributions.  It is symbolic and performs
no scan of a remainder family or Cartesian choice universe. -/
theorem node49_realizedRemainder_mul_hotChoices_le_skeletonCode
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {rate : P13BarrierRateCertificate}
    (aggregate : P13SequentialHotAggregate ctx rate) :
    Nat.card (Core.DependentOwnerGlueCapacity.RealizedProjection
      aggregate.JointState
      (SimpleGraph (P13RemainderVertex ctx)) aggregate.remainderGraph) *
        Nat.card (∀ owner,
          P13RetainedLocalChoice aggregate.retained owner) ≤
      aggregate.codes.card := by
  convert
    (node49RealizedRemainderHotCapacityProfile aggregate).base_mul_localProduct_le_codeCard
    using 1 <;> rfl

/-- Canonical final aggregate already determined by node [21]'s framework
ledger.  This is a mathematical projection of the accumulated fact, not a
second ledger or application-owned transport object. -/
noncomputable def node49CanonicalAggregate {V : Type u}
    {residual : InitialResidual V} (node18 : Node18Stage residual)
    (bounded : Node19Low residual node18)
    (node21 : Node21Output node18 bounded) :
  P13SequentialHotAggregate (Node21Context node18)
      node21.barrierRateCertificate :=
  p13AccumulatedFinalHotAggregate node18 bounded node21

theorem node49CanonicalAggregate_eq {V : Type u}
    {residual : InitialResidual V} (node18 : Node18Stage residual)
    (bounded : Node19Low residual node18)
    (node21 : Node21Output node18 bounded) :
    node49CanonicalAggregate node18 bounded node21 =
      p13SequentialFinalHotAggregate (Node21Context node18)
        node21.barrierRateCertificate := by
  exact p13AccumulatedFinalHotAggregate_eq node18 bounded node21

/-- Node [49]'s sole new certificate.  The family itself is retained so node
[52] can form the framework-owned recoverable join without reconstructing it. -/
structure Node49Output {V : Type u} {residual : InitialResidual V}
    (node18 : Node18Stage residual)
    (_bounded : Node19Low residual node18)
    (node21 : Node21Output node18 _bounded) : Type (u + 2) where
  stateCount : Nat
  stateCountExact : stateCount =
    Nat.card (P13RealizedRemainderState node18 _bounded node21)
  stateCountPos : 0 < stateCount
  entropy : ℝ
  entropyExact : entropy = Real.logb 2 stateCount /
    (p13RemainderVertices (Node21Context node18)).card
  semanticChecks : Nat := 0
  semanticChecksZero : semanticChecks = 0

private noncomputable def node49Output {V : Type u}
    {residual : InitialResidual V} (node18 : Node18Stage residual)
    (bounded : Node19Low residual node18)
    (node21 : Node21Output node18 bounded)
    (low : Node22Low residual node18 bounded node21)
    (node31 : Node31Output node18 bounded node21 low)
    (fullRank : Node32FullRank node18)
    (node48 : Node48Output node18 bounded node21 low node31 fullRank) :
    Node49Output node18 bounded node21 := by
  -- The literal node-[48] payload is the sole incoming application value.
  -- Mentioning its new mathematical conclusion here prevents this successor
  -- from silently reaching around the framework stage to an older node.
  have _forcedCost := node48.forcedCost
  exact {
    stateCount := Nat.card (P13RealizedRemainderState node18 bounded node21)
    stateCountExact := rfl
    stateCountPos := p13RealizedRemainderState_card_pos node18 bounded node21
    entropy := Real.logb 2
        (Nat.card (P13RealizedRemainderState node18 bounded node21)) /
      (p13RemainderVertices (Node21Context node18)).card
    entropyExact := rfl
    semanticChecks := 0
    semanticChecksZero := rfl
  }

abbrev Node49Stage {V : Type u} (residual : InitialResidual V) :=
  Core.ResidualRefinement.State.FocusedBranchDecisionNoContinuation
    (@Node32Bypass V) (@Node32Active V)
    (fun _ data => Node32RankDrop data.previous)
    (fun _ data => Node32FullRank data.previous)
    (fun _ data _fullRank =>
      Node49Output data.previous data.outerProof data.outerOutput) residual

/- Framework-owned successor of the literal node-[48] leaf. Core focuses the
active leaf and preserves both bypass constructors. -/
noncomputable def node49P13RemainderEntropy {V : Type u} {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available (@Node48Stage V)) facts]
    :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      (@Node49Stage V) :=
  Core.ResidualRefinement.State.StageNode.mapFocusedBranchNoContinuation
    (Bypass := @Node32Bypass V)
    (Active := @Node32Active V)
    (yes := fun _ data => Node32RankDrop data.previous)
    (no := fun _ data => Node32FullRank data.previous)
    (Output := fun _ data fullRank => Node48Output data.previous data.outerProof
      data.outerOutput data.innerProof data.current fullRank)
    (Next := fun _ data _fullRank =>
      Node49Output data.previous data.outerProof data.outerOutput)
    fun _residual data fullRank node48 =>
      node49Output data.previous data.outerProof data.outerOutput
        data.innerProof data.current fullRank node48

noncomputable def runInitialThroughNode49 {V : Type u}
    (residual : InitialResidual V) :=
  (runInitialThroughNode48 residual).mapYesStage node49P13RemainderEntropy

def node49LocalChecks : Nat := 0

theorem node49LocalChecks_eq_zero : node49LocalChecks = 0 := rfl

end Erdos64EG.Internal
