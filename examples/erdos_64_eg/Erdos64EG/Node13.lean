import Erdos64EG.Node12
import StructuralExhaustion.Graph.PackedBoundariedGluing

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Diagram node [13]: replacement lemma

The sole new assertion is the paper's literal replacement consequence: a
proper atom cannot admit a smaller one-way obstruction-preserving replacement
with the same boundary degrees and the required internal properties.  The
graph-owned certified CT3 execution proves the contradiction.
-/

abbrev Node13Output {V : Type u} {residual : InitialResidual V}
    (node12 : Node12Stage residual) :=
  ∀ {T : Type u} (boundaries : FinEnum T) [Nonempty T]
    (atom : Node11ProperAtom (Node12Context node12) boundaries)
    (compression :
      Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.Compression
        packedStaticInput boundaries atom), False

abbrev Node13Stage {V : Type u} (residual : InitialResidual V) :=
  Core.ResidualRefinement.State.DependentSuccessor (@Node12Stage V)
    (fun _current node12 => Node13Output node12) residual

abbrev Node13Context {V : Type u} {residual : InitialResidual V}
    (node13 : Node13Stage residual) :=
  Node12Context node13.previous

private noncomputable def node13Output {V : Type u}
    {residual : InitialResidual V} (node12 : Node12Stage residual) :
    Node13Output node12 := by
  intro T boundaries nonempty atom compression
  exact
    Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.Compression.impossible
      compression

noncomputable def node13Replacement {V : Type u} {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available (@Node12Stage V)) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts) (@Node13Stage V) :=
  Core.ResidualRefinement.State.StageNode.mapStage
    (fun _residual node12 => node13Output node12)

noncomputable def runInitialThroughNode13 {V : Type u}
    (residual : InitialResidual V) :=
  (runInitialThroughNode12 residual).mapYesStage node13Replacement

theorem node13_replacement {V : Type u}
    {residual : InitialResidual V} (stage : Node13Stage residual) :
    Node13Output stage.previous :=
  stage.output

def node13LocalChecks : Nat := 0

theorem node13LocalChecks_eq_zero : node13LocalChecks = 0 := rfl

#print axioms node13Replacement
#print axioms node13_replacement

end Erdos64EG.Internal
