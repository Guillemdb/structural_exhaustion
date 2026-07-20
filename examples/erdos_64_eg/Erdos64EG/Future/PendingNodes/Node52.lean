import Erdos64EG.Future.PendingNodes.Node51

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Diagram node [52]: joint window--remainder accounting

The original Part-IV diagram has one edge `[51] -> [52] -> [54]`; node [52]
is not a decision.  Its sole new argument combines the already established
window contribution and the exact node-[51] remainder bits in the same
near-cubic skeleton budget.  The old mathematical output is retained during
the framework migration through one certificate indexed by the literal
node-[50] high leaf and literal node-[51] value.  Consequently this node stays
yellow until that same-context joint-accounting producer is reconstructed.
-/

/-- Exact temporary boundary for the one mathematical proof still owed at
node [52].  It cannot be applied to the node-[50] low leaf, a bypass leaf, a
different node-[51] output, or a different residual. -/
structure Node52JointAccountingCertificate {V : Type u}
    {residual : InitialResidual V} (active : Node50Active V residual)
    (high : Node50High residual active)
    (_node51 : Node51Output active high) : Prop where
  jointBudget : Node24HighEntropyJointBudget active.previous

/-- Explicitly yellow reuse of the old node-[52] joint-accounting output.
This is a temporary proof input, not unconditional evidence for node [52]. -/
structure Node52JointAccountingTypedYellowInput (V : Type u) : Type (u + 3) where
  certificate : ∀ {residual : InitialResidual V}
    (active : Node50Active V residual)
    (high : Node50High residual active)
    (node51 : Node51Output active high),
      Node52JointAccountingCertificate active high node51

/-- The two exact finite assertions established locally at node [52]: the
same-context feasibility inequality and its inherited node-[24] density-cap
consequence. -/
structure Node52Output {V : Type u} {residual : InitialResidual V}
    (active : Node50Active V residual)
    (_high : Node50High residual active) : Type (u + 2) where
  jointBudget : Node24HighEntropyJointBudget active.previous
  thetaBound : Node24HighEntropyCap active.previous

/-- The node-[24] transformer is retrieved as one reusable proposition from
the full accumulated ledger.  Node [52] never reopens node [24]'s dependent
payload or re-proves its packing-support estimate. -/
noncomputable def node52InheritedQuery {V : Type u} {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available (@Node24Stage V)) facts] :
    Core.ResidualRefinement.State.LedgerQuery (facts := facts)
      (@Node24HighEntropyTransformer V) :=
  Core.ResidualRefinement.State.LedgerQuery.entailedStage
    (facts := facts) (Stage := @Node24Stage V)
    (property := @Node24HighEntropyTransformer V)

/-- Exact `[51] -> [52]` successor family; Core retains the bypass and the
node-[50] low leaf literally. -/
abbrev Node52Stage {V : Type u} (residual : InitialResidual V) :=
  Core.ResidualRefinement.State.FocusedBranchDecisionYesContinuation
    (Node50Bypass V) (Node50Active V)
    (@Node50High V) (@Node50Low V)
    (fun residual active high =>
      Node52Output (residual := residual) active high)
    residual

/-- Install the exact old joint-accounting result only on the literal
node-[51] leaf, then use the inherited node-[24] transformer.  Query
resolution and all branch transport are framework-owned. -/
noncomputable def node52P13WindowRemainderAccounting {V : Type u}
    (input : Node52JointAccountingTypedYellowInput V) {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available (@Node51Stage V)) facts]
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available (@Node24Stage V)) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      (@Node52Stage V) :=
  Core.ResidualRefinement.State.StageNode.mapFocusedBranchYesContinuationDerived
      (node52InheritedQuery (V := V) (facts := facts))
      fun _residual transform active high node51 =>
        let accounting := input.certificate active high node51
        {
          jointBudget := accounting.jointBudget
          thetaBound := transform active.previous accounting.jointBudget
        }

noncomputable def runInitialThroughNode52 {V : Type u}
    (quietBlock : Node23DenseWindowQuietBlockInput V)
    (node48Input : Node48TypedYellowInput V)
    (node52Input : Node52JointAccountingTypedYellowInput V)
    (residual : InitialResidual V) :=
  (runInitialThroughNode51 quietBlock node48Input
    residual).mapYesStage
      (node52P13WindowRemainderAccounting node52Input)

/-- Node [52] is symbolic accounting and performs no local semantic scan. -/
def node52LocalChecks : Nat := 0

theorem node52LocalChecks_eq_zero : node52LocalChecks = 0 := rfl

#print axioms node52P13WindowRemainderAccounting
#print axioms runInitialThroughNode52

end Erdos64EG.Internal
