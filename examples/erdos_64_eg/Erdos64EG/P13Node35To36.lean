import Erdos64EG.P13Node33To35
import StructuralExhaustion.Core.ExactHandoff

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Exact context-validity decision `[35] -> [36]`

Node `[36]` audits the raw quotient restricted from the final carrier to the
original proper atom.  The two interfaces remain dependently distinct.  The
proof-level audit returns either one concrete original-interface context or
universal equality at that interface; it never materializes a context family.
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
    Type (u + 3) extends Core.ExactHandoff node35 where
  decision : node35.certificate.OriginalContextAudit
  decisionExact : decision = node35.certificate.auditOriginal
  total : Nonempty node35.certificate.OriginalContextAudit
  localWork :
    node35.certificate.routeBudget.checks () ≤
      node35.certificate.routeBudget.coefficient *
        (node35.certificate.routeBudget.size () + 1) ^
          node35.certificate.routeBudget.degree

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
  decision := node35.certificate.auditOriginal
  decisionExact := rfl
  total := ⟨node35.certificate.auditOriginal⟩
  localWork := node35.certificate.routeBudget.bounded ()

end Erdos64EG.Internal
