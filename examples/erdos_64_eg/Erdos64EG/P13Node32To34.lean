import Erdos64EG.P13Node31To32
import StructuralExhaustion.Core.ExactHandoff

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Exact existing no edge `[32] -> [34]`

Node `[34]` is only the full-curvature-rank residual.  The exact finite no-edge
equality is stronger than the displayed asymptotic lower bound and is retained
without executing the later curvature-cost or Branch-D join.
-/

/-- Complete node-[34] payload indexed by node [32] and its literal no-edge
full-rank equality. -/
structure VerifiedP13Node34FullCurvatureRank
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
    (fullRank : p13CurvatureTargetRank ctx =
      (p13RemainderCurvatureProfile ctx).wedgeCount) : Type (u + 1)
    extends Core.ExactHandoff node32 where
  fullRankExact : p13CurvatureTargetRank ctx =
    (p13RemainderCurvatureProfile ctx).wedgeCount
  noRankLoss : ¬p13CurvatureTargetRank ctx <
    (p13RemainderCurvatureProfile ctx).wedgeCount
  fullRankLower :
    (p13RemainderCurvatureProfile ctx).wedgeCount ≤
      p13CurvatureTargetRank ctx
  maximalFamily :
    ∃ family : Finset (P13CurvatureCoordinate ctx),
      (p13CurvatureResponseProfile ctx).ct15Profile.Survives family ∧
        family.card = (p13RemainderCurvatureProfile ctx).wedgeCount
  localWork :
    (p13CurvatureResponseProfile ctx).ct15Profile.rankDecisionBudget.checks () ≤
      (p13CurvatureResponseProfile ctx).ct15Profile.rankDecisionBudget.coefficient *
        ((p13CurvatureResponseProfile ctx).ct15Profile.rankDecisionBudget.size () + 1) ^
          (p13CurvatureResponseProfile ctx).ct15Profile.rankDecisionBudget.degree

/-- Execute only the manuscript's full-rank no edge. -/
noncomputable def VerifiedP13Node32RankDecision.node34
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
    (fullRank : p13CurvatureTargetRank ctx =
      (p13RemainderCurvatureProfile ctx).wedgeCount) :
    VerifiedP13Node34FullCurvatureRank
      ctx node21 node24 node26 node27 node28 node29 node30 node31 node32 fullRank := by
  exact {
    previous := node32
    previousExact := rfl
    fullRankExact := fullRank
    noRankLoss := Nat.not_lt_of_ge fullRank.ge
    fullRankLower := fullRank.ge
    maximalFamily := by
      obtain ⟨family, survives, familyCard⟩ :=
        (p13CurvatureResponseProfile ctx).ct15Profile.exists_surviving_card_eq_targetRank
      exact ⟨family, survives, familyCard.trans fullRank⟩
    localWork :=
      (p13CurvatureResponseProfile ctx).ct15Profile.rankDecisionBudget.bounded ()
  }

end Erdos64EG.Internal
