import Erdos64EG.P13Node36To38

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Exact proper-compression terminal `[38] -> [39]`

Node `[38]` has already retained the certified strictly smaller representative
required by admission of its non-injective quotient.  Node `[39]` applies the
framework minimality closure to that exact predecessor field.  It performs no
new inspection and creates no additional branch.
-/

/-- The original node-[39] proper-atom compression terminal, indexed by the
exact node-[38] yes-edge payload. -/
theorem VerifiedP13Node38ProperRepresentativeDecision.node39
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
    (node38 : VerifiedP13Node38ProperRepresentativeDecision
      ctx node21 node24 node26 node27 node28 node29 node30 node31 node32 rankDrop
        node35 node36) : False :=
  node38.representative.impossible

end Erdos64EG.Internal
