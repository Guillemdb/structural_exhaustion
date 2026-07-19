import Erdos64EG.Node8NoProperCore
import StructuralExhaustion.Graph.MinimumDegreeCycleCriticality

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Diagram node [9]: edge-deletion criticality

This node consumes the literal node-[8] stage and attaches the pointwise
consequence of the graph-owned deletion-only CT2 theorem on its avoiding
constructor: every edge has a degree-three endpoint.  The opposite C1
terminal is preserved unchanged by the framework stage combinator.
-/

/-- The sole new node-[9] payload, indexed by the exact node-[8] stage. -/
abbrev Node9Output {V : Type u} {residual : InitialResidual V}
    (node8 : Node8Stage residual) :=
  match node8.output with
  | .c1 _run => PUnit
  | .avoiding _run output => ∀ dart : output.context.G.object.graph.Dart,
      output.context.G.object.degree dart.fst = 3 ∨
        output.context.G.object.degree dart.snd = 3

/-- Stable framework successor type exposed to node `[10]`. -/
abbrev Node9Stage {V : Type u} (residual : InitialResidual V) :=
  Core.ResidualRefinement.State.DependentSuccessor
    (fun current => Node8Stage (V := V) current)
    (fun _current node8 => Node9Output node8) residual

/-- Attach node `[9]` to the exact node-[8] avoiding stage. -/
noncomputable def node9DeletionCriticality {V : Type u} {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available
        (fun current => Node8Stage (V := V) current)) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      (fun current => Node9Stage (V := V) current) :=
  Core.ResidualRefinement.State.StageNode.mapStage fun _residual node8 =>
    match node8.output with
    | .c1 _run => PUnit.unit
    | .avoiding _run output =>
        (Graph.PackedMinimumDegreeCycle.deletionCriticalityFacts
          packedStaticInput output.context).tightEndpoint

/-- Reusable degree-three endpoint consequence produced at node `[9]`. -/
abbrev Node9DegreeThreeEndpointFact {V : Type u}
    (residual : InitialResidual V) : Prop :=
  ∃ node8 : Node8Stage residual,
    match node8.output with
    | .c1 _run => True
    | .avoiding _run output => ∀ dart : output.context.G.object.graph.Dart,
        output.context.G.object.degree dart.fst = 3 ∨
          output.context.G.object.degree dart.snd = 3

instance {V : Type u} :
    Core.ResidualRefinement.State.StageEntails
      (@Node9Stage V) (@Node9DegreeThreeEndpointFact V) where
  prove stage := by
    refine ⟨stage.previous, ?_⟩
    cases prior : stage.previous.output with
    | c1 run => trivial
    | avoiding run output =>
        simpa [Node9Output, prior] using stage.output

/-- Continue only the live avoiding branch through node `[9]`. -/
noncomputable def runInitialThroughNode9 {V : Type u}
    (residual : InitialResidual V) :=
  (runInitialThroughNode8 residual).mapYesStage node9DeletionCriticality

/-- Direct manuscript-facing projection of the degree-three endpoint fact. -/
theorem node9_everyEdgeTouchesDegreeThree {V : Type u}
    {residual : InitialResidual V} (stage : Node9Stage residual) :
    match stage.previous.output with
    | .c1 _run => True
    | .avoiding _run output => ∀ dart : output.context.G.object.graph.Dart,
        output.context.G.object.degree dart.fst = 3 ∨
          output.context.G.object.degree dart.snd = 3 := by
  cases prior : stage.previous.output with
  | c1 run => trivial
  | avoiding run output =>
      simpa [Node9Output, prior] using stage.output

#print axioms runInitialThroughNode9
#print axioms node9_everyEdgeTouchesDegreeThree

end Erdos64EG.Internal
