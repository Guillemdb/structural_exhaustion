import Erdos64EG.InternalProblem
import StructuralExhaustion.Core.MinimalSelection

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Diagram node [4]: minimal-counterexample selection

This node continues only the literal yes edge of node `[2]`.  The framework
retrieves that branch proof from the accumulated ledger, selects a rank-minimal
target-avoiding graph, and appends the selected context as the sole new stage.
-/

/-- The thin node-[4] payload supplied by the generic minimal-selection
successor.  Its bound refers to the graph in the stable node-[1] residual. -/
abbrev Node4Output {V : Type u} (residual : InitialResidual V) :=
  Core.MinimalCounterexampleSelection (problem V) (@Target V)
    ((problem V).rank residual.object)

/-- The exact node-[2] yes-branch query. -/
def node4CounterexampleQuery {V : Type u} {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.CounterexampleBranch.Yes
        (P := problem V) (Target := @Target V) InitialResidual.object) facts] :
    Core.ResidualRefinement.State.LedgerQuery (facts := facts)
      (Core.CounterexampleBranch.Yes
        (P := problem V) (Target := @Target V) InitialResidual.object) :=
  Core.ResidualRefinement.State.LedgerQuery.fact

private def node4AvoidingContext {V : Type u}
    (residual : InitialResidual V) (counterexample : IsCounterexample residual.object) :
    Core.AvoidingContext (problem V) (@Target V) :=
  Core.AvoidingContext.ofBranch {
    G := residual.object
    baseline := counterexample.1
    state := ()
  } counterexample.2

private def node4RankBound {V : Type u} (residual : InitialResidual V) : Nat :=
  (problem V).rank residual.object

private theorem node4AvoidingContext_rank {V : Type u}
    (residual : InitialResidual V) (counterexample : IsCounterexample residual.object) :
    (problem V).rank (node4AvoidingContext residual counterexample).G =
      node4RankBound residual :=
  rfl

/-- Node `[4]` as a framework successor of the exact node-[2] yes stage. -/
noncomputable def node4MinimalSelection {V : Type u} {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.CounterexampleBranch.Yes
        (P := problem V) (Target := @Target V) InitialResidual.object) facts] :
  Core.ResidualRefinement.State.StageNode (facts := facts) (@Node4Output V) :=
  Core.ResidualRefinement.State.StageNode.selectMinimalCounterexample
    (P := problem V) (Target := @Target V)
    (Residual := InitialResidual V)
    node4CounterexampleQuery node4AvoidingContext node4RankBound
    node4AvoidingContext_rank
    (fun _object => ())

/-- Execute node `[4]` only on node `[2]`'s positive branch.  The negative
node-[3] terminal is retained byte-for-byte by `BranchResult.mapYesStage`. -/
noncomputable def runInitialThroughNode4 {V : Type u}
    (residual : InitialResidual V) :=
  (runInitialCounterexampleDecision residual).mapYesStage node4MinimalSelection

/-- The selected node-[4] context is rank-minimal and no larger than the
literal node-[1] graph on the exact positive branch. -/
theorem runInitialThroughNode4_minimal {V : Type u}
    (residual : InitialResidual V) :
    match runInitialThroughNode4 residual with
    | .yesBranch branch =>
        (problem V).rank
            (branch.state.requireStage (Stage := @Node4Output V)).context.G ≤
          (problem V).rank residual.object
    | .noBranch _branch => True := by
  unfold runInitialThroughNode4
  cases runInitialCounterexampleDecision residual with
  | yesBranch branch =>
      let advanced := branch.runStage node4MinimalSelection
      let selection := advanced.state.requireStage
        (Stage := @Node4Output V)
      have bound := selection.rank_le
      have residual_eq : advanced.state.residual = residual := advanced.residualExact
      exact bound.trans_eq
        (congrArg (fun current : InitialResidual V =>
          (problem V).rank current.object) residual_eq)
  | noBranch _branch => trivial

/-- Node `[4]` performs proof-level well-ordering only. -/
def node4LocalChecks : Nat := 0

theorem node4LocalChecks_eq_zero : node4LocalChecks = 0 := rfl

#print axioms runInitialThroughNode4_minimal

end Erdos64EG.Internal
