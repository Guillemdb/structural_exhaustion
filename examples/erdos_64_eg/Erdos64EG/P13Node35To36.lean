import Erdos64EG.P13Node33To35
import StructuralExhaustion.Core.ExactHandoff

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Exact context-validity decision `[35] -> [36]`

Node `[36]` inspects the already admitted quotient carried by Branch D.  The
generic CT15 pair-circuit projection proves that its identified raw wedges have
equal target response in every declared outside context.  No outside-context
family is materialized; the original target-defect edge remains represented by
the decision type and is proved impossible for this admitted payload.
-/

/-- Complete node-[36] payload indexed by the exact green node-[35] residual. -/
structure VerifiedP13Node36ContextValidity
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
      ctx node21 node24 node26 node27 node28 node29 node30 node31 node32 rankDrop) :
    Type (u + 1) extends Core.ExactHandoff node35 where
  decision : node35.circuit.ContextDecision
  decisionExact : decision = .universal node35.circuit.contextUniversal
  validEveryOutsideContext :
    ∀ outside : (p13CurvatureResponseProfile ctx).responseSystem.Context,
      (p13CurvatureResponseProfile ctx).responseSystem.response
          node35.circuit.basisCoordinate outside =
        (p13CurvatureResponseProfile ctx).responseSystem.response
          node35.circuit.determined outside
  noTargetDefect :
    ¬∃ outside : (p13CurvatureResponseProfile ctx).responseSystem.Context,
      (p13CurvatureResponseProfile ctx).responseSystem.response
          node35.circuit.basisCoordinate outside ≠
        (p13CurvatureResponseProfile ctx).responseSystem.response
          node35.circuit.determined outside
  localWork :
    (node35.circuit.contextDecisionBudget).checks () ≤
      (node35.circuit.contextDecisionBudget).coefficient *
        ((node35.circuit.contextDecisionBudget).size () + 1) ^
          (node35.circuit.contextDecisionBudget).degree

/-- Execute the original node-[36] context-validity test on the exact admitted
pair circuit inherited from node [35]. -/
noncomputable def VerifiedP13Node33RankReducingDependence.node36
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
    (node35 : VerifiedP13Node35BranchD
      ctx node21 node24 node26 node27 node28 node29 node30 node31 node32 rankDrop) :
    VerifiedP13Node36ContextValidity
      ctx node21 node24 node26 node27 node28 node29 node30 node31 node32 rankDrop
        node35 where
  previous := node35
  previousExact := rfl
  decision := node35.circuit.contextDecision
  decisionExact := node35.circuit.contextDecision_isUniversal
  validEveryOutsideContext := node35.circuit.contextUniversal
  noTargetDefect := node35.circuit.noContextDefect
  localWork := node35.circuit.contextDecisionBudget.bounded ()

end Erdos64EG.Internal
