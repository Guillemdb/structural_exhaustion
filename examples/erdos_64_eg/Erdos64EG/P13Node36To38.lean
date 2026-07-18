import Erdos64EG.P13Node35To36
import StructuralExhaustion.Core.ExactHandoff

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Exact smaller-representative decision `[36] -> [38]`

The yes edge of node `[36]` retains universal outside-context validity.  Node
`[38]` then reads the representative clause already stored in the admitted,
non-injective pair circuit.  That clause supplies a certified strictly smaller
baseline object with target transport; no candidate representative is searched.
-/

/-- Complete node-[38] payload indexed by the exact node-[36] universal edge. -/
structure VerifiedP13Node38ProperRepresentativeDecision
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx)
    (node24 : VerifiedP13Node24FiniteDensityHandoff ctx node21)
    (node26 : VerifiedP13Node26RemainderContinuation ctx node21 node24)
    (node27 : VerifiedP13Node27NoInternalThreeCore ctx node21 node24 node26)
    (node28 : VerifiedP13Node28PositiveDeficiency
      ctx node21 node24 node26 node27)
    (node29 : VerifiedP13Node29ExternalIncidenceSupply
      ctx node21 node24 node26 node27 node28)
    (node30 : VerifiedP13Node30WedgeLower
      ctx node21 node24 node26 node27 node28 node29)
    (node31 : VerifiedP13Node31CurvatureTargetRank
      ctx node21 node24 node26 node27 node28 node29 node30)
    (node32 : VerifiedP13Node32RankDecision
      ctx node21 node24 node26 node27 node28 node29 node30 node31)
    (rankDrop : p13CurvatureTargetRank ctx <
      (p13RemainderCurvatureProfile ctx).wedgeCount)
    (node35 : VerifiedP13Node35BranchD
      ctx node21 node24 node26 node27 node28 node29 node30 node31 node32 rankDrop)
    (node36 : VerifiedP13Node36ContextValidity
      ctx node21 node24 node26 node27 node28 node29 node30 node31 node32 rankDrop
        node35) : Type (u + 1) extends Core.ExactHandoff node36 where
  contextUniversalExact : previous.validEveryOutsideContext =
    node35.circuit.contextUniversal
  decision : node35.circuit.RepresentativeDecision
  decisionExact : decision =
    .available node35.circuit.smallerRepresentative
  representative : Core.CertifiedReduction ctx
  representativeExact : representative = node35.circuit.smallerRepresentative
  strictlySmaller :
    PackedProblem.rank representative.reduction.value < PackedProblem.rank ctx.G
  baselinePreserved : PackedProblem.Baseline representative.reduction.value
  targetTransport : PackedTarget representative.reduction.value → PackedTarget ctx.G
  localWork :
    node35.circuit.representativeDecisionBudget.checks () ≤
      node35.circuit.representativeDecisionBudget.coefficient *
        (node35.circuit.representativeDecisionBudget.size () + 1) ^
          node35.circuit.representativeDecisionBudget.degree

/-- Execute the original node-[38] representative test on the exact universal
node-[36] output. -/
noncomputable def VerifiedP13Node36ContextValidity.node38
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    {node24 : VerifiedP13Node24FiniteDensityHandoff ctx node21}
    {node26 : VerifiedP13Node26RemainderContinuation ctx node21 node24}
    {node27 : VerifiedP13Node27NoInternalThreeCore ctx node21 node24 node26}
    {node28 : VerifiedP13Node28PositiveDeficiency
      ctx node21 node24 node26 node27}
    {node29 : VerifiedP13Node29ExternalIncidenceSupply
      ctx node21 node24 node26 node27 node28}
    {node30 : VerifiedP13Node30WedgeLower
      ctx node21 node24 node26 node27 node28 node29}
    {node31 : VerifiedP13Node31CurvatureTargetRank
      ctx node21 node24 node26 node27 node28 node29 node30}
    {node32 : VerifiedP13Node32RankDecision
      ctx node21 node24 node26 node27 node28 node29 node30 node31}
    {rankDrop : p13CurvatureTargetRank ctx <
      (p13RemainderCurvatureProfile ctx).wedgeCount}
    {node35 : VerifiedP13Node35BranchD
      ctx node21 node24 node26 node27 node28 node29 node30 node31 node32 rankDrop}
    (node36 : VerifiedP13Node36ContextValidity
      ctx node21 node24 node26 node27 node28 node29 node30 node31 node32 rankDrop
        node35) :
    VerifiedP13Node38ProperRepresentativeDecision
      ctx node21 node24 node26 node27 node28 node29 node30 node31 node32 rankDrop
        node35 node36 where
  previous := node36
  previousExact := rfl
  contextUniversalExact := rfl
  decision := node35.circuit.representativeDecision
  decisionExact := node35.circuit.representativeDecision_isAvailable
  representative := node35.circuit.smallerRepresentative
  representativeExact := rfl
  strictlySmaller := node35.circuit.smallerRepresentative.reduction.decreases
  baselinePreserved := node35.circuit.smallerRepresentative.reducedBaseline
  targetTransport := node35.circuit.smallerRepresentative.targetMonotone
  localWork := node35.circuit.representativeDecisionBudget.bounded ()

end Erdos64EG.Internal
