import Erdos64EG.Node16
import StructuralExhaustion.Graph.InducedPathMaximalPacking

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Diagram node [17]: maximal disjoint induced-`P₁₃` packing

Node [16] has already eliminated the `P₁₃`-free constructor of the
node-[15] decision.  Thus the literal node-[16] stage contains precisely the
surviving non-free branch.  This module reuses the already verified
proof-selected packing but exposes only CT12's maximal-only view:
disjointness, saturation, exhausted selected-list execution, trace, totality,
and linear selected-list work.  The application defines no handoff or ledger
and cannot access a maximum-cardinality field through its node output.
-/

theorem node17ThirteenPositive : 0 < 13 := by decide

/-- The selected minimal graph carried by the literal node-[16] survivor. -/
abbrev Node17Context {V : Type u} {residual : InitialResidual V}
    (node16 : Node16Stage residual) :=
  Node15Context node16.previous

/-- The sole new node-[17] payload: CT12's maximal-only view of the selected
packing on node [15]'s surviving no branch. -/
abbrev Node17Output {V : Type u} {residual : InitialResidual V}
    (node16 : Node16Stage residual) :=
  Graph.InducedPathMaximalPacking.VerifiedStage
    (Node17Context node16).G.object 13 node17ThirteenPositive
      (Node17Context node16).toBranchContext

/-- Node [17] is the framework-owned dependent successor of the literal
node-[16] surviving stage. -/
abbrev Node17Stage {V : Type u} (residual : InitialResidual V) :=
  Core.ResidualRefinement.State.DependentSuccessor
    (@Node16Stage V)
    (fun _current node16 => Node17Output node16)
    residual

/-- Public context projection for consumers of the literal node-[17] stage. -/
abbrev Node17StageContext {V : Type u} {residual : InitialResidual V}
    (node17 : Node17Stage residual) :=
  Node17Context node17.previous

/-- Public selected-window projection.  Consumers need not reconstruct any
earlier predecessor path. -/
noncomputable def node17Windows {V : Type u}
    {residual : InitialResidual V} (node17 : Node17Stage residual) :=
  Graph.InducedPathMaximalPacking.windows
    (Node17StageContext node17).G.object 13 node17ThirteenPositive

/-- Public size of the exact selected maximal family. -/
noncomputable def node17PackingNumber {V : Type u}
    {residual : InitialResidual V} (node17 : Node17Stage residual) : Nat :=
  (node17Windows node17).length

/-- Execute CT12 and append its verified packing stage to the one accumulated
ledger. The application supplies only the fixed path length. -/
noncomputable def node17InducedP13Packing {V : Type u} {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available (@Node16Stage V)) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      (@Node17Stage V) :=
  Core.ResidualRefinement.State.StageNode.mapStage fun _residual node16 =>
    Graph.InducedPathMaximalPacking.verifiedStage
      (Node17Context node16).G.object 13 node17ThirteenPositive
        (Node17Context node16).toBranchContext

/-- Continue the sole surviving node-[16] stage through node [17]. -/
noncomputable def runInitialThroughNode17 {V : Type u}
    (residual : InitialResidual V) :=
  (runInitialThroughNode16 residual).mapYesStage node17InducedP13Packing

/-- The selected packing is maximal, exactly as required by node [17]. -/
theorem node17_maximal {V : Type u} {residual : InitialResidual V}
    (stage : Node17Stage residual) :
    ∀ window : Graph.InducedPathMaximalPacking.Window
        (Node17Context stage.previous).G.object 13,
      ∃ selected ∈
          Graph.InducedPathMaximalPacking.windows
            (Node17Context stage.previous).G.object 13
              node17ThirteenPositive,
        ¬Disjoint
          (Graph.InducedPathMaximalPacking.support
            (Node17Context stage.previous).G.object 13 window)
          (Graph.InducedPathMaximalPacking.support
            (Node17Context stage.previous).G.object 13 selected) :=
  stage.output.saturated

/-- CT12 exhausts exactly the selected packing schedule. -/
theorem node17_terminal {V : Type u} {residual : InitialResidual V}
    (stage : Node17Stage residual) :
    (Graph.InducedPathMaximalPacking.run
      (Node17Context stage.previous).G.object 13 node17ThirteenPositive
        (Node17Context stage.previous).toBranchContext).terminal =
            .exhausted :=
  stage.output.terminal

/-- The framework-owned CT12 packing audit is total. -/
noncomputable def node17Total {V : Type u} {residual : InitialResidual V}
    (stage : Node17Stage residual) :=
  stage.output.total

/-- Reusable framework-owned polynomial certificate for node [17]'s local
selected-list audit. -/
noncomputable def node17WorkBudget {V : Type u}
    {residual : InitialResidual V} (stage : Node17Stage residual) :
    Core.PolynomialCheckBudget Unit :=
  Graph.InducedPathMaximalPacking.workBudget
    (Node17Context stage.previous).G.object 13 node17ThirteenPositive
    (Node17Context stage.previous).toBranchContext

/-- The no certificate retained by node [16] says that the selected graph
contains an induced `P₁₃`; maximality therefore selects at least one
window. -/
theorem node17_nonempty {V : Type u} {residual : InitialResidual V}
    (stage : Node17Stage residual) :
    Graph.InducedPathMaximalPacking.windows
      (Node17Context stage.previous).G.object 13 node17ThirteenPositive ≠ [] := by
  apply Graph.InducedPathMaximalPacking.windows_nonempty_of_realization
  exact Classical.byContradiction stage.previous.proof

#print axioms node17InducedP13Packing
#print axioms node17_maximal
#print axioms node17_terminal
#print axioms node17Total
#print axioms node17_nonempty

end Erdos64EG.Internal
