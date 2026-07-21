import Erdos64EG.Node31

namespace Erdos64EG.Internal
open StructuralExhaustion
universe u

/-!
# Diagram node [32]: the CT15 curvature-rank dichotomy

Node [31] defines the exact proof-level support-stratified CT15 rank.  This
node executes that profile's exhaustive strict-loss/full-cardinality split.
The yes edge is the rank-drop residual consumed by Branch D; the no edge is
the exact finite full-rank certificate consumed by Residual B.  Core owns the
two branch carriers and preserves the one accumulated ledger.
-/

/-- Node [32]'s yes edge is CT15's literal strict rank-loss proposition on
the single manuscript curvature rank. -/
abbrev Node32RankDrop {V : Type u} {r : InitialResidual V}
    (n18 : Node18Stage r) : Prop :=
  (p13CurvatureRankProfile (Node21Context n18)).targetRank <
    (p13CurvatureCoordinates (Node21Context n18)).card

/-- Node [32]'s no edge is CT15's exact full-cardinality certificate.  The
weaker asymptotic inequality displayed in the paper follows immediately. -/
abbrev Node32FullRank {V : Type u} {r : InitialResidual V}
    (n18 : Node18Stage r) : Prop :=
  (p13CurvatureRankProfile (Node21Context n18)).targetRank =
    (p13CurvatureCoordinates (Node21Context n18)).card

/-- The proof-relevant CT15 decision used by node [32].  This is a projection
of the node-[31] rank profile, not an application-owned threshold test. -/
noncomputable def node32RankDecision {V : Type u} {r : InitialResidual V}
    (n18 : Node18Stage r) :=
  (p13CurvatureRankProfile (Node21Context n18)).rankDecision

/-- Read CT15's proof-relevant decision as the decidability evidence consumed
by Core's accumulated-ledger branch executor. -/
noncomputable def node32RankDropDecidable {V : Type u}
    {r : InitialResidual V} (n18 : Node18Stage r) :
    Decidable (Node32RankDrop n18) := by
  cases node32RankDecision n18 with
  | dropped rank_lt => exact isTrue rank_lt
  | full rank_eq => exact isFalse (Nat.not_lt_of_ge rank_eq.ge)

/-- The two exact CT15 outcomes are exhaustive. -/
theorem node32RankDecision_exhaustive {V : Type u}
    {r : InitialResidual V} (n18 : Node18Stage r) :
    Node32RankDrop n18 ∨ Node32FullRank n18 :=
  (p13CurvatureRankProfile (Node21Context n18))
    |>.rankDecision_exhaustive

abbrev Node32Bypass {V : Type u} :=
  Core.ResidualRefinement.State.DependentDecisionOnNoNoAfterYesBypass
    (@Node18Stage V) (@Node19High V) (@Node19Low V)
    (fun _ n18 b => Node21Output n18 b) (@Node22High V)
    (fun _ n18 b n21 high => Node23Output n18 b n21 high)

abbrev Node32Active {V : Type u} :=
  Core.ResidualRefinement.State.DependentDecisionOnNoNoAfterYesActive
    (@Node18Stage V) (@Node19Low V)
    (fun _ n18 b => Node21Output n18 b) (@Node22Low V)
    (fun _ n18 b n21 low => Node31Output n18 b n21 low)

abbrev Node32Stage {V : Type u} (r : InitialResidual V) :=
  Core.ResidualRefinement.State.FocusedBranchDecision
    (@Node32Bypass V) (@Node32Active V)
    (fun _ data => Node32RankDrop data.previous)
    (fun _ data => Node32FullRank data.previous) r

noncomputable def node32P13RankDropDecision {V : Type u} {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available (@Node31Stage V)) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts) (@Node32Stage V) :=
  Core.ResidualRefinement.State.StageNode.decideDependentDecisionOnNoNoAfterYes
    (Current := fun _ n18 bounded node21 low =>
      Node31Output n18 bounded node21 low)
    (yes := fun _ data => Node32RankDrop data.previous)
    (no := fun _ data => Node32FullRank data.previous)
    (fun _ data => node32RankDropDecidable data.previous)
    (fun _ data absent => by
      exact Nat.le_antisymm
        (p13CurvatureRankProfile
          (Node21Context data.previous)).targetRank_le_coordinates
        (Nat.le_of_not_gt absent))

noncomputable def runInitialThroughNode32 {V : Type u}
    (residual : InitialResidual V) :=
  (runInitialThroughNode31 residual).mapYesStage
    node32P13RankDropDecision

def node32LocalChecks : Nat := 0
theorem node32LocalChecks_eq_zero : node32LocalChecks = 0 := rfl

theorem node32RankDecisionWork_eq_zero {V : Type u}
    {residual : InitialResidual V} (node18 : Node18Stage residual) :
    ((p13CurvatureRankProfile (Node21Context node18))
        |>.rankDecisionBudget).checks () = 0 :=
  rfl

#print axioms node32RankDecision_exhaustive
#print axioms node32RankDecisionWork_eq_zero
#print axioms node32P13RankDropDecision
#print axioms runInitialThroughNode32
end Erdos64EG.Internal
