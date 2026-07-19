import Erdos64EG.P13Node35To36
import StructuralExhaustion.Core.ExactHandoff

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Exact target-defect terminal `[36] -> [37]`

The no edge of node `[36]` retains one concrete context belonging to the
original atom interface.  This is a terminal target-defect payload, not a
contradiction obtained by importing carrier-level universality.
-/

structure P13Node37TargetDefect
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
        node35) : Type (u + 3) extends Core.ExactHandoff node36 where
  context : (p13CurvatureDeterminationSupportProfile ctx).Context
    node35.certificate.original
  mismatch :
    (p13CurvatureDeterminationSupportProfile ctx).response
        node35.certificate.original node35.certificate.basisCoordinate context ≠
      (p13CurvatureDeterminationSupportProfile ctx).response
        node35.certificate.original node35.certificate.determined context
  decisionEdge : previous.decision =
    .defective context mismatch

/-- Construct exactly node `[36]`'s concrete-defect edge. -/
def VerifiedP13Node36ContextValidity.node37
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
        node35)
    (context : (p13CurvatureDeterminationSupportProfile ctx).Context
      node35.certificate.original)
    (mismatch :
      (p13CurvatureDeterminationSupportProfile ctx).response
          node35.certificate.original node35.certificate.basisCoordinate context ≠
        (p13CurvatureDeterminationSupportProfile ctx).response
          node35.certificate.original node35.certificate.determined context)
    (edge : node36.decision = .defective context mismatch) :
    P13Node37TargetDefect node36 where
  previous := node36
  previousExact := rfl
  context := context
  mismatch := mismatch
  decisionEdge := edge

/-- Node `[37]` exposes the exact target-response mismatch at the original
atom interface. -/
theorem P13Node37TargetDefect.targetDefective
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
    {node36 : VerifiedP13Node36ContextValidity
      ctx node21 node24 node26 node27 node28 node29 node30 node31 node32 rankDrop
        node35}
    (node37 : P13Node37TargetDefect node36) :
    ∃ context : (p13CurvatureDeterminationSupportProfile ctx).Context
        node35.certificate.original,
      (p13CurvatureDeterminationSupportProfile ctx).response
          node35.certificate.original node35.certificate.basisCoordinate context ≠
        (p13CurvatureDeterminationSupportProfile ctx).response
          node35.certificate.original node35.certificate.determined context :=
  ⟨node37.context, node37.mismatch⟩

end Erdos64EG.Internal
