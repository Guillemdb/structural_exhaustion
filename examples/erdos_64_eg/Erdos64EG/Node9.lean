import Erdos64EG.Node8
import StructuralExhaustion.Graph.MinimumDegreeCycleCriticality

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Diagram node [9]: edge-deletion criticality

The node consumes the literal node-[8] successor.  Its only new payload is the
pointwise deletion-criticality conclusion that every edge has a degree-three
endpoint.  The graph layer owns the deletion-only CT2 argument.
-/

abbrev Node9Output {V : Type u} {residual : InitialResidual V}
    (node8 : Node8Stage residual) :=
  ∀ dart : node8.output.context.G.object.graph.Dart,
    node8.output.context.G.object.degree dart.fst = 3 ∨
      node8.output.context.G.object.degree dart.snd = 3

abbrev Node9Stage {V : Type u} (residual : InitialResidual V) :=
  Core.ResidualRefinement.State.DependentSuccessor (@Node8Stage V)
    (fun _current node8 => Node9Output node8) residual

abbrev Node9Context {V : Type u} {residual : InitialResidual V}
    (node9 : Node9Stage residual) :=
  node9.previous.output.context

private noncomputable def node9Output {V : Type u}
    {residual : InitialResidual V} (node8 : Node8Stage residual) :
    Node9Output node8 := by
  simpa [packedStaticInput] using
    (Graph.PackedMinimumDegreeCycle.deletionCriticalityFacts
      packedStaticInput node8.output.context).tightEndpoint

noncomputable def node9DeletionCriticality {V : Type u} {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available (@Node8Stage V)) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts) (@Node9Stage V) :=
  Core.ResidualRefinement.State.StageNode.mapStage
    (fun _residual node8 => node9Output node8)

abbrev Node9DegreeThreeEndpointFact {V : Type u}
    (residual : InitialResidual V) : Prop :=
  ∃ node8 : Node8Stage residual, Node9Output node8

instance {V : Type u} :
    Core.ResidualRefinement.State.StageEntails
      (@Node9Stage V) (@Node9DegreeThreeEndpointFact V) where
  prove stage := ⟨stage.previous, stage.output⟩

noncomputable def runInitialThroughNode9 {V : Type u}
    (residual : InitialResidual V) :=
  (runInitialThroughNode8 residual).mapYesStage node9DeletionCriticality

theorem node9_everyEdgeTouchesDegreeThree {V : Type u}
    {residual : InitialResidual V} (stage : Node9Stage residual) :
    Node9Output stage.previous :=
  stage.output

#print axioms runInitialThroughNode9
#print axioms node9_everyEdgeTouchesDegreeThree

end Erdos64EG.Internal
