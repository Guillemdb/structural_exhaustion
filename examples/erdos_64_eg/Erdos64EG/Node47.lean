import Erdos64EG.Node46

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Diagram node [47]: full-rank Residual B

Node [47] is the cross-panel occurrence of the exact node-[34] no leaf after
the rank-drop branch has been accumulated and closed.  Its only payload is the
paper's Residual-B full-rank consequence on the same literal node-[32] no
constructor; Core owns all routing and ledger preservation.
-/

/-- Node [47]'s sole new public consequence: Residual B is on the full
declared-curvature-rank leaf. -/
structure Node47Output {V : Type u} {residual : InitialResidual V}
    (node18 : Node18Stage residual)
    (_bounded : Node19Low residual node18)
    (_node21 : Node21Output node18 _bounded)
    (_low : Node22Low residual node18 _bounded _node21)
    (_node31 : Node31Output node18 _bounded _node21 _low)
    (_fullRank : Node32FullRank node18) : Type (u + 1) where
  fullRankExact : Node32FullRank node18
  targetRank_eq_coordinateLength :
    p13CurvatureTargetRank (Node21Context node18) =
      (p13CurvatureCoordinates
        (Node21Context node18)).toOrderedCollection.values.length

/-- Node [47] keeps the same focused no leaf and appends only the Residual-B
full-rank consequence. -/
abbrev Node47Stage {V : Type u} (residual : InitialResidual V) :=
  Core.ResidualRefinement.State.FocusedBranchDecisionNoContinuation
    (@Node32Bypass V) (@Node32Active V)
    (fun _ data => Node32RankDrop data.previous)
    (fun _ data => Node32FullRank data.previous)
    (fun _ data fullRank => Node47Output data.previous data.outerProof
      data.outerOutput data.innerProof data.current fullRank)
    residual

/-- Framework-owned cross-panel continuation. -/
noncomputable def node47P13FullRankContinuation {V : Type u} {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available (@Node32Stage V)) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      (@Node47Stage V) :=
  Core.ResidualRefinement.State.StageNode.continueFocusedBranchNo
    fun _residual data fullRank =>
      {
        fullRankExact := fullRank
        targetRank_eq_coordinateLength := by
          simpa [p13CurvatureTargetRank, Node32FullRank,
            FinEnum.toOrderedCollection_length] using fullRank
      }

noncomputable def runInitialThroughNode47 {V : Type u}
    (residual : InitialResidual V) :=
  (runInitialThroughNode46 residual).mapYesStage
    node47P13FullRankContinuation

def node47LocalChecks : Nat := 0

theorem node47LocalChecks_eq_zero : node47LocalChecks = 0 := rfl

#print axioms node47P13FullRankContinuation
#print axioms runInitialThroughNode47

end Erdos64EG.Internal
