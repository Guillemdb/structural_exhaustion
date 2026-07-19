import Erdos64EG.P13Node31To32
import StructuralExhaustion.Core.ExactHandoff

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Exact existing yes edge `[32] -> [33]`

The strict-loss edge extracts one finite functional dependence circuit from
the exact maximum-survival rank.  The circuit carries an admitted quotient,
two distinct declared raw coordinates with the same quotient value, and the
singleton determining basis.  No quotient or subfamily family is searched.
-/

/-- Complete node-[33] payload indexed by node [32] and its literal yes-edge
rank-loss proof. -/
structure VerifiedP13Node33RankReducingDependence
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
      (p13RemainderCurvatureProfile ctx).wedgeCount) : Type (u + 3)
    extends Core.ExactHandoff node32 where
  rankDropExact : p13CurvatureTargetRank ctx <
    (p13RemainderCurvatureProfile ctx).wedgeCount
  circuit : (p13CurvatureDeterminationRankProfile ctx).PairCircuit
  circuitExact : circuit =
    (p13CurvatureDeterminationRankProfile ctx).pairCircuitOfRankDrop (by
      exact False.elim (no_p13CanonicalCurvature_rankDrop ctx rankDrop))
  certificate : (p13CurvatureDeterminationSupportProfile ctx).Certificate
  certificateExact : certificate =
    CT15.SupportStratifiedRank.Profile.certificate
      (p13CurvatureDeterminationRankProfile ctx) circuit
  carrierExact : certificate.carrier = circuit.candidate.carrier
  finiteBasis : circuit.basis.card = 1
  properDependence : circuit.basisCoordinate ≠ circuit.determined
  quotientIdentifies :
    circuit.candidate.quotientCode circuit.basisCoordinate =
      circuit.candidate.quotientCode circuit.determined
  originalEligible :
    (p13CurvatureDeterminationSupportProfile ctx).originalEligible
      certificate.original
  carrierConnected :
    (p13CurvatureDeterminationSupportProfile ctx).connected certificate.carrier
  supportMinimal : ∀ support,
    (p13CurvatureDeterminationSupportProfile ctx).connected support →
    (p13CurvatureDeterminationSupportProfile ctx).determines support
      certificate.basisCoordinate certificate.determined →
    (p13CurvatureDeterminationSupportProfile ctx).supportLe support
      certificate.carrier →
    (p13CurvatureDeterminationSupportProfile ctx).supportLe certificate.carrier
      support
  localWork :
    (p13CurvatureDeterminationRankProfile ctx).rankDecisionBudget.checks () ≤
      (p13CurvatureDeterminationRankProfile ctx).rankDecisionBudget.coefficient *
        ((p13CurvatureDeterminationRankProfile ctx).rankDecisionBudget.size () + 1) ^
          (p13CurvatureDeterminationRankProfile ctx).rankDecisionBudget.degree

/-- Execute only the manuscript's strict-loss edge to Branch D. -/
noncomputable def VerifiedP13Node32RankDecision.node33
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
    (node32 : VerifiedP13Node32RankDecision
      ctx node21 node24 node26 node27 node28 node29 node30 node31)
    (rankDrop : p13CurvatureTargetRank ctx <
      (p13RemainderCurvatureProfile ctx).wedgeCount) :
    VerifiedP13Node33RankReducingDependence
      ctx node21 node24 node26 node27 node28 node29 node30 node31 node32 rankDrop := by
  exact False.elim (no_p13CanonicalCurvature_rankDrop ctx rankDrop)

end Erdos64EG.Internal
