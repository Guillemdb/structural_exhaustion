import Erdos64EG.Node154
import Erdos64EG.Shared.CT1

namespace Erdos64EG.Internal

open StructuralExhaustion
open StructuralExhaustion.Graph
open StructuralExhaustion.Graph.InducedPathColdCorridor

universe u

/-!
# Diagram node [155]: G1 dyadic-cycle terminal

Node [155] consumes the G1 yes leaf produced by node [154].  The selected
first-failure hit already carries a graph-owned power-of-two cycle certificate,
so the node only projects that certificate through the existing CT1 surface and
closes the branch against the inherited target-avoiding context.
-/

abbrev Node155Stage {V : Type u} (residual : InitialResidual V) :=
  Core.ResidualRefinement.State.FocusedBranchDecisionYesClosed
    (Core.ResidualRefinement.State.FocusedBranchDecisionNoContinuationBypass
      (Node148Bypass V) (Node148Active V)
      (@Node148LiveHotCap V) (@Node148LiveHotFailure V))
    (Node154LiveLeaf V) (@Node154G1Hit V) (@Node154NoG1 V) residual

theorem node155G1_ct1_certificate {V : Type u}
    {residual : InitialResidual V} (active : Node154LiveLeaf V residual)
    (g1 : Node154G1Hit active) :
    let ctx := Node21Context active.data.node18
    ∃ run : CT1.CertifiedC1Run (ct1Spec ctx.G.Vertex)
        (ct1Input ctx.G.object ctx.baseline),
      run.result.terminal = .c1 ∧
      run.result.trace =
        [.entry, .equivalenceCertification, .realizationDecision,
          .c1Terminal] ∧
      run.checks = 1 := by
  rcases g1 with ⟨entry, _member, vertex, _stageMember, proof⟩
  let ctx := Node21Context active.data.node18
  let data :=
    InducedPathColdCorridor.targetHitOfF1
      (node153CorridorProducer active.data) PowerOfTwoLength entry vertex proof
  refine ⟨runCT1 ctx.G.object ctx.baseline data.cycle, ?_, ?_, ?_⟩
  · exact (runCT1 ctx.G.object ctx.baseline data.cycle).terminal_eq
  · exact (runCT1 ctx.G.object ctx.baseline data.cycle).trace_eq
  · exact (runCT1 ctx.G.object ctx.baseline data.cycle).checks_eq

theorem node155G1_impossible {V : Type u}
    {residual : InitialResidual V} (active : Node154LiveLeaf V residual)
    (g1 : Node154G1Hit active) : False := by
  let ctx := Node21Context active.data.node18
  rcases g1 with ⟨entry, _member, vertex, _stageMember, proof⟩
  let data :=
    InducedPathColdCorridor.targetHitOfF1
      (node153CorridorProducer active.data) PowerOfTwoLength entry vertex proof
  exact ctx.avoids ⟨data.cycle⟩

noncomputable def node155G1DyadicCycleClosure {V : Type u} {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available (@Node154DecisionStage V))
        facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      (@Node155Stage V) :=
  Core.ResidualRefinement.State.StageNode.closeFocusedBranchYes
    (fun _residual active g1 => node155G1_impossible active g1)

noncomputable def runInitialThroughNode155 {V : Type u}
    (residual : InitialResidual V) :=
  ((runInitialThroughNode153 residual).mapYesStage
    node154GermCaseDecision).mapYesStage
      node155G1DyadicCycleClosure

def node155LocalChecks : Nat := 0

theorem node155LocalChecks_eq_zero : node155LocalChecks = 0 := rfl

#print axioms node155G1_ct1_certificate
#print axioms node155G1_impossible
#print axioms node155G1DyadicCycleClosure
#print axioms runInitialThroughNode155

end Erdos64EG.Internal
