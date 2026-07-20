import Erdos64EG.Node4
import Erdos64EG.TargetAlgebra

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Diagram node [5]: edge-rooted Mersenne target algebra

This node consumes the literal minimal-counterexample selection produced at
node `[4]`.  It adds only the target/return equivalence and its target-avoiding
specialization to the one accumulated ledger.  No edge, path, graph, or
context family is inspected.
-/

/-- The sole new mathematical payload at node `[5]`, indexed by node `[4]`'s
actual selected minimal counterexample. -/
structure Node5TargetAlgebra {V : Type u}
    (ctx : Core.MinimalCounterexampleContext (problem V) (@Target V)) :
    Type (u + 1) where
  targetIffReturn : Target ctx.G ↔ HasMersenneReturn ctx.G.graph
  returnSetsDisjoint : ∀ dart : ctx.G.graph.Dart,
    Disjoint (returnSet ctx.G.graph dart) MersenneSet

/-- Node `[5]` is the dependent successor of the literal node-`[4]` stage. -/
abbrev Node5Stage {V : Type u} (residual : InitialResidual V) :=
  Core.ResidualRefinement.State.DependentSuccessor
    (@Node4Output V)
    (fun _residual node4 =>
      Node5TargetAlgebra (packedStaticInput.fixedContext node4.context))
    residual

/-- Construct only node `[5]`'s graph-specific target algebra.  Target
avoidance is read from node `[4]`'s selected context rather than rederived. -/
noncomputable def node5TargetAlgebra {V : Type u} {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available (@Node4Output V)) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts) (@Node5Stage V) :=
  Core.ResidualRefinement.State.StageNode.mapStage fun _residual node4 =>
    { targetIffReturn := target_iff_hasMersenneReturn
        (packedStaticInput.fixedContext node4.context).G
      returnSetsDisjoint :=
        (not_target_iff_returnSets_disjoint
          (packedStaticInput.fixedContext node4.context).G).mp
          (packedStaticInput.fixedContext node4.context).avoids }

/-- Reusable proposition exported from node `[5]`.  The existential packages
the exact node-`[4]` selection retained by the framework successor; consumers
that need its dependent data query `Node5Stage` itself. -/
abbrev Node5TargetAlgebraFact {V : Type u}
    (residual : InitialResidual V) : Prop :=
  ∃ node4 : Node4Output residual,
    (Target (packedStaticInput.fixedContext node4.context).G ↔
        HasMersenneReturn
          (packedStaticInput.fixedContext node4.context).G.graph) ∧
      ∀ dart : (packedStaticInput.fixedContext node4.context).G.graph.Dart,
        Disjoint (returnSet
          (packedStaticInput.fixedContext node4.context).G.graph dart) MersenneSet

instance {V : Type u} :
    Core.ResidualRefinement.State.StageEntails
      (@Node5Stage V) (@Node5TargetAlgebraFact V) where
  prove stage :=
    ⟨stage.previous, stage.output.targetIffReturn,
      stage.output.returnSetsDisjoint⟩

/-- Continue only the exact node-`[4]` branch and retain node `[3]` unchanged. -/
noncomputable def runInitialThroughNode5 {V : Type u}
    (residual : InitialResidual V) :=
  (runInitialThroughNode4 residual).mapYesStage node5TargetAlgebra

/-- Node `[5]` performs no primitive checks. -/
def node5LocalChecks : Nat := 0

theorem node5LocalChecks_eq_zero : node5LocalChecks = 0 := rfl

#print axioms runInitialThroughNode5

end Erdos64EG.Internal
