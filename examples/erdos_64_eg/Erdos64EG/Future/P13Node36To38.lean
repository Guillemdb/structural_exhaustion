import Erdos64EG.Future.P13Node35To36
import StructuralExhaustion.Core.ExactHandoff

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Original-support location decision `[36] -> [38]`

After node `[36]` has certified universal response at the original atom
interface, node `[38]` tests whether the certificate's final carrier is that
same atom or is a strict connected enlargement.  The carrier-indexed
representative is transported to the atom only in the equality constructor.
-/

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
        node35) : Type (u + 3) extends Core.ExactHandoff node36 where
  allContexts : ∀ context :
      (p13CurvatureDeterminationSupportProfile ctx).Context
        node35.certificate.original,
    (p13CurvatureDeterminationSupportProfile ctx).response
        node35.certificate.original node35.certificate.basisCoordinate context =
      (p13CurvatureDeterminationSupportProfile ctx).response
        node35.certificate.original node35.certificate.determined context
  contextEdge : previous.decision = .universal allContexts
  location : node35.certificate.Location
  locationExact : location = node35.certificate.location
  localWork :
    node35.certificate.routeBudget.checks () ≤
      node35.certificate.routeBudget.coefficient *
        (node35.certificate.routeBudget.size () + 1) ^
          node35.certificate.routeBudget.degree

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
        node35)
    (allContexts : ∀ context :
      (p13CurvatureDeterminationSupportProfile ctx).Context
        node35.certificate.original,
      (p13CurvatureDeterminationSupportProfile ctx).response
          node35.certificate.original node35.certificate.basisCoordinate context =
        (p13CurvatureDeterminationSupportProfile ctx).response
          node35.certificate.original node35.certificate.determined context)
    (edge : node36.decision = .universal allContexts) :
    VerifiedP13Node38ProperRepresentativeDecision
      ctx node21 node24 node26 node27 node28 node29 node30 node31 node32 rankDrop
        node35 node36 where
  previous := node36
  previousExact := rfl
  allContexts := allContexts
  contextEdge := edge
  location := node35.certificate.location
  locationExact := rfl
  localWork := node35.certificate.routeBudget.bounded ()

end Erdos64EG.Internal
