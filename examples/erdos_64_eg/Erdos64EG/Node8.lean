import Erdos64EG.Node7
import Erdos64EG.Shared.CT2
import StructuralExhaustion.CT1.ResidualRefinement

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Diagram node [8]: no proper minimum-degree-three subgraph

The framework consumes node `[7]`'s sole live avoiding successor.  From its
retained minimal context it executes packed minimality and CT2 proper-subgraph
reduction, appending the resulting no-proper-core certificate to the same
accumulated ledger.
-/

/-- The one new node-[8] payload, indexed by the exact node-[7] successor. -/
abbrev Node8Output {V : Type u} {residual : InitialResidual V}
    (node7 : Node7Stage residual) :=
  packedStaticInput.SelectedNoProperCore
    node7.previous.previous.context.G.object

/-- Stable framework successor type exposed to node `[9]`. -/
abbrev Node8Stage {V : Type u} (residual : InitialResidual V) :=
  Core.ResidualRefinement.State.DependentSuccessor (@Node7Stage V)
    (fun _current node7 => Node8Output node7) residual

/-- Node `[8]` consumes node `[7]`'s literal live successor and invokes the
framework-owned packed-minimality/CT2 executor. -/
noncomputable def node8NoProperCore {V : Type u} {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available
        (fun current => Node7Stage (V := V) current)) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      (fun current => Node8Stage (V := V) current) :=
  Core.ResidualRefinement.State.StageNode.mapStage
    (fun _residual node7 =>
      Graph.PackedMinimumDegreeCycle.StaticInput.selectNoProperCore
        packedStaticInput node7.previous.previous.context.G.object
        node7.previous.previous.context.baseline
        node7.previous.previous.context.avoids)

/-- Continue the live counterexample branch through node `[8]`; all terminal
branches are transported by framework combinators. -/
noncomputable def runInitialThroughNode8 {V : Type u}
    (residual : InitialResidual V) :=
  (runInitialThroughNode7 residual).mapYesStage node8NoProperCore

/-- The node-[8] avoiding successor excludes every proper subgraph retaining
minimum degree three. -/
theorem node8_noProperCore {V : Type u} {residual : InitialResidual V}
    (node7 : Node7Stage residual)
    (output : Node8Output node7) :
    ∀ subgraph : Graph.PackedFiniteObject.ProperSubgraph output.context.G,
      ¬packedStaticInput.problem.Baseline subgraph.value :=
  output.certificate.noProperCore

/-- Each hypothetical proper-core contradiction is the exact CT2 deletion-C2
terminal with its typed trace, total execution, and constant work bound. -/
theorem node8_ct2_certificate {V : Type u}
    {residual : InitialResidual V} (node7 : Node7Stage residual)
    (output : Node8Output node7)
    (subgraph : Graph.PackedFiniteObject.ProperSubgraph output.context.G)
    (baseline : packedStaticInput.problem.Baseline subgraph.value) :
    (packedStaticInput.properSubgraphCT2Run output.context subgraph baseline).terminal =
        .deletionC2 ∧
      (packedStaticInput.properSubgraphCT2Run output.context subgraph baseline).trace =
        [.entry, .deletionDecision, .deletionC2Terminal] ∧
      (packedStaticInput.properSubgraphCT2Run output.context subgraph baseline).checks = 1 :=
  ⟨output.certificate.properCoreTerminal subgraph baseline,
    output.certificate.properCoreTrace subgraph baseline,
    output.certificate.properCoreChecks subgraph baseline⟩

#print axioms runInitialThroughNode8
#print axioms node8_noProperCore
#print axioms node8_ct2_certificate

end Erdos64EG.Internal
