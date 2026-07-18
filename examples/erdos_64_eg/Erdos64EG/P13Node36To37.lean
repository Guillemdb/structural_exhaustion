import Erdos64EG.P13Node35To36

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Exact target-defect terminal `[36] -> [37]`

The no edge of node `[36]` carries one concrete outside context on which the
two identified raw wedges have different exact target responses.  The generic
CT15 defect payload retains that witness.  Since the node-[35] quotient was
already admitted, node `[36]` also proves universal equality, and this edge
closes immediately without searching another context.
-/

/-- Literal target-defect payload on the exact node-[35] pair circuit. -/
abbrev P13Node37TargetDefect
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
      ctx node21 node24 node26 node27 node28 node29 node30 node31 node32 rankDrop) :=
  node35.circuit.ContextDefect

/-- The terminal payload is exactly one concrete distinguishing outside
context, with no reconstructed response object. -/
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
    (defect : P13Node37TargetDefect node35) :
    ∃ outside : (p13CurvatureResponseProfile ctx).responseSystem.Context,
      (p13CurvatureResponseProfile ctx).responseSystem.response
          node35.circuit.basisCoordinate outside ≠
        (p13CurvatureResponseProfile ctx).responseSystem.response
          node35.circuit.determined outside :=
  defect.toExists

/-- Execute and close only node `[36]`'s target-defect edge. -/
theorem VerifiedP13Node36ContextValidity.node37
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
    (_node36 : VerifiedP13Node36ContextValidity
      ctx node21 node24 node26 node27 node28 node29 node30 node31 node32 rankDrop
        node35)
    (defect : P13Node37TargetDefect node35) : False :=
  defect.impossible

end Erdos64EG.Internal
