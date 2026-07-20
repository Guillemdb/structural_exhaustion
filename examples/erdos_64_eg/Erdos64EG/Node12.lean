import Erdos64EG.Node11
import StructuralExhaustion.Graph.PackedBoundariedGluing

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Diagram node [12]: context universality

This node consumes the literal node-[11] atom/profile stage and adds only the
context-universality implication for target-complete identifications.
-/

abbrev Node12Output {V : Type u} {residual : InitialResidual V}
    (node11 : Node11Stage residual) :=
  ∀ {T : Type u} (boundaries : FinEnum T) [Nonempty T]
    (left right : Node11ProperAtom (Node11Context node11) boundaries),
      Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.TargetComplete
          packedStaticInput boundaries left.source right.source →
        Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.ContextEquivalent
          packedStaticInput boundaries left.source right.source

abbrev Node12Stage {V : Type u} (residual : InitialResidual V) :=
  Core.ResidualRefinement.State.DependentSuccessor (@Node11Stage V)
    (fun _current node11 => Node12Output node11) residual

abbrev Node12Context {V : Type u} {residual : InitialResidual V}
    (node12 : Node12Stage residual) :=
  Node11Context node12.previous

private noncomputable def node12Output {V : Type u}
    {residual : InitialResidual V} (node11 : Node11Stage residual) :
    Node12Output node11 := by
  intro T boundaries nonempty left right complete
  exact
    Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.targetComplete_contextUniversal
      packedStaticInput boundaries complete

noncomputable def node12ContextUniversality {V : Type u} {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available (@Node11Stage V)) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts) (@Node12Stage V) :=
  Core.ResidualRefinement.State.StageNode.mapStage
    (fun _residual node11 => node12Output node11)

noncomputable def runInitialThroughNode12 {V : Type u}
    (residual : InitialResidual V) :=
  (runInitialThroughNode11 residual).mapYesStage node12ContextUniversality

theorem node12_context_universal {V : Type u}
    {residual : InitialResidual V} (stage : Node12Stage residual) :
    Node12Output stage.previous :=
  stage.output

def node12LocalChecks : Nat := 0

theorem node12LocalChecks_eq_zero : node12LocalChecks = 0 := rfl

#print axioms node12ContextUniversality
#print axioms node12_context_universal

end Erdos64EG.Internal
