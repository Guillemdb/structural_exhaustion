import Erdos64EG.Node9

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Diagram node [10]: independence of high-degree vertices

This successor consumes node `[9]`'s exact endpoint theorem and adds only its
pointwise graph-local consequence: vertices of degree at least four are
independent.
-/

abbrev Node10Output {V : Type u} {residual : InitialResidual V}
    (node9 : Node9Stage residual) : Prop :=
  ∀ {left right : (Node9Context node9).G.Vertex},
    4 ≤ (Node9Context node9).G.object.degree left →
    4 ≤ (Node9Context node9).G.object.degree right →
      ¬(Node9Context node9).G.object.graph.Adj left right

abbrev Node10Stage {V : Type u} (residual : InitialResidual V) :=
  Core.ResidualRefinement.State.DependentSuccessor (@Node9Stage V)
    (fun _current node9 => Node10Output node9) residual

/-- The live graph context, obtained through node `[10]`'s literal immediate
predecessor.  Successors use this indexed view instead of reopening an older
ledger entry. -/
abbrev Node10Context {V : Type u} {residual : InitialResidual V}
    (node10 : Node10Stage residual) :=
  Node9Context node10.previous

private noncomputable def node10Output {V : Type u}
    {residual : InitialResidual V} (node9 : Node9Stage residual) :
    Node10Output node9 := by
  have endpoint : ∀ dart : (Node9Context node9).G.object.graph.Dart,
      (Node9Context node9).G.object.degree dart.fst =
          packedStaticInput.minimumDegree ∨
        (Node9Context node9).G.object.degree dart.snd =
          packedStaticInput.minimumDegree := by
    simpa [packedStaticInput] using node9.output
  intro left right leftHigh rightHigh
  exact Graph.PackedMinimumDegreeCycle.slackVerticesIndependent_of_tightEndpoint
    packedStaticInput (Node9Context node9) endpoint
      (by simpa [packedStaticInput] using leftHigh)
      (by simpa [packedStaticInput] using rightHigh)

noncomputable def node10HighDegreeIndependence {V : Type u} {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available (@Node9Stage V)) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts) (@Node10Stage V) :=
  Core.ResidualRefinement.State.StageNode.mapStage
    (fun _residual node9 => node10Output node9)

abbrev Node10HighDegreeIndependentFact {V : Type u}
    (residual : InitialResidual V) : Prop :=
  ∃ node9 : Node9Stage residual, Node10Output node9

instance {V : Type u} :
    Core.ResidualRefinement.State.StageEntails
      (@Node10Stage V) (@Node10HighDegreeIndependentFact V) where
  prove stage := ⟨stage.previous, stage.output⟩

noncomputable def runInitialThroughNode10 {V : Type u}
    (residual : InitialResidual V) :=
  (runInitialThroughNode9 residual).mapYesStage node10HighDegreeIndependence

theorem node10_highDegreeVerticesIndependent {V : Type u}
    {residual : InitialResidual V} (stage : Node10Stage residual) :
    Node10Output stage.previous :=
  stage.output

def node10LocalChecks : Nat := 0

theorem node10LocalChecks_eq_zero : node10LocalChecks = 0 := rfl

#print axioms runInitialThroughNode10
#print axioms node10_highDegreeVerticesIndependent

end Erdos64EG.Internal
