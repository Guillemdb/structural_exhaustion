import Erdos64EG.Node30
import Erdos64EG.Shared.CT15RemainderCurvature
import Erdos64EG.Shared.P13RealizedRemainderResponse

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Diagram node [31]: curvature target-rank

This node appends the exact response semantics, declared-coordinate count,
rank bound, and a maximal surviving coordinate witness to the incoming
node-[30] residual.  It does not choose a branch.  The immediately following
node [32] executes CT15's proof-relevant rank dichotomy on this same profile.
-/

structure Node31Facts {V : Type u} {residual : InitialResidual V}
    (node18 : Node18Stage residual)
    (_bounded : Node19Low residual node18)
    (_node21 : Node21Output node18 _bounded)
    (_low : Node22Low residual node18 _bounded _node21) : Type (u + 2) where
  coordinateCount :
    (p13CurvatureCoordinates (Node21Context node18)).card =
      (p13RemainderCurvatureProfile (Node21Context node18)).wedgeCount
  responseExact : ∀ coordinate outside,
    (p13CurvatureResponseProfile
      (Node21Context node18)).responseSystem.response coordinate outside = true ↔
      packedStaticInput.Target
        (Graph.PackedBoundariedGluing.glue
          (Node21Context node18).G.object.input.vertices
          ((p13CurvatureResponseProfile
            (Node21Context node18)).coordinatePiece coordinate) outside)
  realizedResponseExact : ∀ coordinate state,
    p13RealizedRemainderResponse
        (node18 := node18) (bounded := _bounded) (node21 := _node21)
        coordinate state = true ↔
      packedStaticInput.Target
        (Graph.PackedBoundariedGluing.glue
          (Node21Context node18).G.object.input.vertices
          ((p13CurvatureResponseProfile
            (Node21Context node18)).coordinatePiece coordinate)
          (Graph.FiniteSupportOutsideContext.context
            (p13RealizedRemainderAmbientObject state)
            (p13CurvatureSupport coordinate)))
  targetRankBound :
    p13CurvatureTargetRank (Node21Context node18) ≤
      (p13RemainderCurvatureProfile (Node21Context node18)).wedgeCount
  maximalSurvivingCoordinates :
    ∃ coordinates : Finset (P13CurvatureCoordinate (Node21Context node18)),
      (p13CurvatureRankProfile
        (Node21Context node18)).Survives coordinates ∧
      coordinates.card = p13CurvatureTargetRank (Node21Context node18)

/-- Node [31] retains the literal node-[30] certificate through Core's
proof-relevant successor carrier.  Later nodes can therefore retrieve every
node-[30] inequality without a checkpoint or caller input. -/
abbrev Node31Output {V : Type u} {residual : InitialResidual V}
    (node18 : Node18Stage residual)
    (bounded : Node19Low residual node18)
    (node21 : Node21Output node18 bounded)
    (low : Node22Low residual node18 bounded node21) :=
  Core.ResidualRefinement.State.DependentSuccessor
    (fun _ => Node30Output node18 bounded node21 low)
    (fun _ _ => Node31Facts node18 bounded node21 low) residual

namespace Node31Output
abbrev coordinateCount (output : Node31Output node18 bounded node21 low) :
    (p13CurvatureCoordinates (Node21Context node18)).card =
      (p13RemainderCurvatureProfile (Node21Context node18)).wedgeCount :=
  output.output.coordinateCount

abbrev node30 (output : Node31Output node18 bounded node21 low) :
    Node30Output node18 bounded node21 low := output.previous

end Node31Output

abbrev Node31Stage {V : Type u} (residual : InitialResidual V) :=
  Core.ResidualRefinement.State.DependentDecisionOnNoNoAfterYes
    (@Node18Stage V) (@Node19High V) (@Node19Low V)
    (fun _residual node18 bounded => Node21Output node18 bounded)
    (@Node22High V) (@Node22Low V)
    (fun _residual node18 bounded node21 high =>
      Node23Output node18 bounded node21 high)
    (fun _residual node18 bounded node21 low =>
      Node31Output node18 bounded node21 low) residual

noncomputable def node31P13CurvatureTargetRank {V : Type u} {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available (@Node30Stage V)) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      (@Node31Stage V) :=
  Core.ResidualRefinement.State.StageNode.accumulateDependentDecisionOnNoNoAfterYes
    (Current := fun _ node18 bounded node21 low => Node30Output node18 bounded node21 low)
    (Next := fun _ node18 bounded node21 low _node30 =>
      Node31Facts node18 bounded node21 low)
    fun _residual node18 bounded node21 low
        (node30 : Node30Output node18 bounded node21 low) => by
      have _ := node30.remainderWedgeFloor
      exact {
        coordinateCount :=
          p13CurvatureCoordinates_card_eq_wedgeCount (Node21Context node18)
        responseExact :=
          (p13CurvatureResponseProfile (Node21Context node18)).response_true_iff
        realizedResponseExact :=
          p13RealizedRemainderResponse_true_iff
        targetRankBound :=
          p13CurvatureTargetRank_le_wedgeCount (Node21Context node18)
        maximalSurvivingCoordinates :=
          exists_p13Curvature_surviving_card_eq_targetRank (Node21Context node18)
      }

noncomputable def runInitialThroughNode31 {V : Type u}
    (residual : InitialResidual V) :=
  (runInitialThroughNode30 residual).mapYesStage
    node31P13CurvatureTargetRank

def node31LocalChecks : Nat := 0
theorem node31LocalChecks_eq_zero : node31LocalChecks = 0 := rfl

#print axioms node31P13CurvatureTargetRank
#print axioms runInitialThroughNode31

end Erdos64EG.Internal
