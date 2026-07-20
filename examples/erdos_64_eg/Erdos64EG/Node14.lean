import Erdos64EG.Node13
import StructuralExhaustion.Graph.PackedBoundariedGluing

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Diagram node [14]: hereditary target-uncompressibility

This node derives the two clauses of the manuscript corollary from the exact
node-[13] replacement theorem and node-[12] context universality: no proper
atom has a nontrivial target-complete compression, and a context-defective
identification is both non-target-complete and explicitly distinguished.
-/

structure Node14Output {V : Type u} {residual : InitialResidual V}
    (node13 : Node13Stage residual) : Prop where
  noTargetCompleteCompression :
    ∀ {T : Type u} (boundaries : FinEnum T) [Nonempty T]
      (atom : Node11ProperAtom (Node13Context node13) boundaries)
      (piece : Graph.PackedBoundariedGluing.Piece T)
      (complete :
        Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.TargetComplete
          packedStaticInput boundaries piece atom.source)
      (internalTargetFree :
        ¬ packedStaticInput.Target
          (Graph.PackedBoundariedGluing.Piece.pack boundaries piece))
      (internalBaseline : piece.InternalBaseline boundaries
        packedStaticInput.minimumDegree)
      (locallySmaller :
        Graph.PackedBoundariedGluing.Piece.LexSmaller piece atom.source), False
  defectiveIdentification :
    ∀ {T : Type u} (boundaries : FinEnum T) [Nonempty T]
      (left right : Node11ProperAtom
        (Node13Context node13) boundaries),
      ¬ Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.ContextEquivalent
          packedStaticInput boundaries left.source right.source →
        (¬ Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.TargetComplete
            packedStaticInput boundaries left.source right.source) ∧
          Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.TargetDefective
            packedStaticInput boundaries left.source right.source

abbrev Node14Stage {V : Type u} (residual : InitialResidual V) :=
  Core.ResidualRefinement.State.DependentSuccessor (@Node13Stage V)
    (fun _current node13 => Node14Output node13) residual

private noncomputable def node14Output {V : Type u}
    {residual : InitialResidual V} (node13 : Node13Stage residual) :
    Node14Output node13 := by
  constructor
  · intro T boundaries nonempty atom piece complete internalTargetFree
      internalBaseline locallySmaller
    exact node13.output boundaries atom
      (Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.Compression.ofTargetComplete
        (input := packedStaticInput) (boundaries := boundaries) (atom := atom)
        piece complete internalTargetFree internalBaseline locallySmaller)
  · intro T boundaries nonempty left right notEquivalent
    constructor
    · intro complete
      exact notEquivalent (node13.previous.output boundaries left right complete)
    · exact
        Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.targetDefective_of_not_contextEquivalent
          packedStaticInput boundaries notEquivalent

noncomputable def node14Uncompressibility {V : Type u} {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available (@Node13Stage V)) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts) (@Node14Stage V) :=
  Core.ResidualRefinement.State.StageNode.mapStage
    (fun _residual node13 => node14Output node13)

noncomputable def runInitialThroughNode14 {V : Type u}
    (residual : InitialResidual V) :=
  (runInitialThroughNode13 residual).mapYesStage node14Uncompressibility

theorem node14_uncompressible {V : Type u}
    {residual : InitialResidual V} (stage : Node14Stage residual) :
    Node14Output stage.previous :=
  stage.output

def node14LocalChecks : Nat := 0

theorem node14LocalChecks_eq_zero : node14LocalChecks = 0 := rfl

#print axioms node14Uncompressibility
#print axioms node14_uncompressible

end Erdos64EG.Internal
