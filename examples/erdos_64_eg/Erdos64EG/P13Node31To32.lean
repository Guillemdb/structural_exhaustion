import Erdos64EG.P13Node30To31
import StructuralExhaustion.Core.ExactHandoff

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Exact existing node `[32]` rank decision

The node consumes the exact target-rank object from `[31]` and takes precisely
the two original diagram edges: strict loss from the complete raw wedge
schedule, or equality with that schedule.  The comparison is proof-level and
does not enumerate coordinate subfamilies, quotients, or contexts.
-/

/-- Complete node-[32] payload indexed by the literal node-[31] output. -/
structure VerifiedP13Node32RankDecision
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
      ctx node21 node24 node26 node27 node28 node29 node30) : Type (u + 3)
    extends Core.ExactHandoff node31 where
  decision : (p13CurvatureFunctionalRankProfile ctx).RankDecision
  decisionExact : decision =
    (p13CurvatureFunctionalRankProfile ctx).rankDecision
  rankDropOrFull :
    p13CurvatureTargetRank ctx <
        (p13RemainderCurvatureProfile ctx).wedgeCount ∨
      p13CurvatureTargetRank ctx =
        (p13RemainderCurvatureProfile ctx).wedgeCount
  localWork :
    (p13CurvatureFunctionalRankProfile ctx).rankDecisionBudget.checks () ≤
      (p13CurvatureFunctionalRankProfile ctx).rankDecisionBudget.coefficient *
        ((p13CurvatureFunctionalRankProfile ctx).rankDecisionBudget.size () + 1) ^
          (p13CurvatureFunctionalRankProfile ctx).rankDecisionBudget.degree

/-- Execute only the manuscript's node-[32] dichotomy. -/
noncomputable def VerifiedP13Node31CurvatureTargetRank.node32
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
    (node31 : VerifiedP13Node31CurvatureTargetRank
      ctx node21 node24 node26 node27 node28 node29 node30) :
    VerifiedP13Node32RankDecision
      ctx node21 node24 node26 node27 node28 node29 node30 node31 where
  previous := node31
  previousExact := rfl
  decision := (p13CurvatureFunctionalRankProfile ctx).rankDecision
  decisionExact := rfl
  rankDropOrFull := by
    have split :=
      (p13CurvatureFunctionalRankProfile ctx).rankDecision_exhaustive
    change p13CurvatureTargetRank ctx < (p13CurvatureCoordinates ctx).card ∨
      p13CurvatureTargetRank ctx = (p13CurvatureCoordinates ctx).card at split
    rw [p13CurvatureCoordinates_card_eq_wedgeCount ctx] at split
    exact split
  localWork :=
    (p13CurvatureFunctionalRankProfile ctx).rankDecisionBudget.bounded ()

end Erdos64EG.Internal
