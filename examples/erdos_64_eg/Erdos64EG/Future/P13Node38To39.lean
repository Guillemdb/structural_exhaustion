import Erdos64EG.Future.P13Node36To38

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Exact proper-compression terminal `[38] -> [39]`

Only the literal at-original constructor transports the carrier representative
to the proper atom.  The graph specialization then executes its stored CT3
compression and closes by minimality.
-/

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
        node35 node36)
    (equal : node35.certificate.carrier = node35.certificate.original)
    (edge : node38.location = .atOriginal equal) : False := by
  let edgeWitness := edge
  clear edgeWitness
  let representative := node35.certificate.originalRepresentative equal
  exact
    Graph.SupportStratifiedDetermination.Representative.impossible_of_originalEligible
      node35.originalEligible representative

end Erdos64EG.Internal
