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
      (p13RemainderCurvatureProfile ctx).wedgeCount) : Type (u + 1)
    extends Core.ExactHandoff node32 where
  rankDropExact : p13CurvatureTargetRank ctx <
    (p13RemainderCurvatureProfile ctx).wedgeCount
  circuit : (p13CurvatureResponseProfile ctx).ct15Profile.PairCircuit
  circuitExact : circuit =
    (p13CurvatureResponseProfile ctx).ct15Profile.pairCircuitOfRankDrop (by
      change (p13CurvatureResponseProfile ctx).ct15Profile.targetRank <
        (p13CurvatureCoordinates ctx).card
      rw [p13CurvatureCoordinates_card_eq_wedgeCount ctx]
      exact rankDrop)
  finiteBasis : circuit.basis.card = 1
  properDependence : circuit.basisCoordinate ≠ circuit.determined
  quotientIdentifies :
    circuit.proposal.code circuit.basisCoordinate =
      circuit.proposal.code circuit.determined
  localWork :
    (p13CurvatureResponseProfile ctx).ct15Profile.rankDecisionBudget.checks () ≤
      (p13CurvatureResponseProfile ctx).ct15Profile.rankDecisionBudget.coefficient *
        ((p13CurvatureResponseProfile ctx).ct15Profile.rankDecisionBudget.size () + 1) ^
          (p13CurvatureResponseProfile ctx).ct15Profile.rankDecisionBudget.degree

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
  have coordinateDrop :
      (p13CurvatureResponseProfile ctx).ct15Profile.targetRank <
        (p13CurvatureCoordinates ctx).card := by
    change p13CurvatureTargetRank ctx < (p13CurvatureCoordinates ctx).card
    rw [p13CurvatureCoordinates_card_eq_wedgeCount ctx]
    exact rankDrop
  let circuit :=
    (p13CurvatureResponseProfile ctx).ct15Profile.pairCircuitOfRankDrop
      coordinateDrop
  exact {
    previous := node32
    previousExact := rfl
    rankDropExact := rankDrop
    circuit := circuit
    circuitExact := rfl
    finiteBasis := by simp [circuit,
      CT15.AdmissibleQuotient.Profile.PairCircuit.basis]
    properDependence := circuit.distinct
    quotientIdentifies := circuit.determines
    localWork :=
      (p13CurvatureResponseProfile ctx).ct15Profile.rankDecisionBudget.bounded ()
  }

end Erdos64EG.Internal
