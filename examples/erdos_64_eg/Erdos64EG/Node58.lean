import Erdos64EG.Node57

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Diagram node [58]: net charge

Node [58] names the exact quarter-scaled net-charge numerator on the identical
large-budget residual carried by node [57].  The manuscript object uses the
remainder surplus `σ_R`; this node consumes node [57]'s produced numerator
instead of recomputing a separate value.  The total-surplus numerator is
not a node-[58] object.
The node does not inspect components or perform the node-[59] nonnegativity
split.
-/

/-- Node [58]'s sole new payload: the manuscript net-charge notation, in the
finite quarter-scaled form consumed by the next split. -/
structure Node58Output {V : Type u} {residual : InitialResidual V}
    (active : Node50Active V residual)
    (node56 : Node56Output active)
    (_node57 : Node57Output active node56) : Type (u + 2) where
  /-- The manuscript numerator
  `4 * (def⁺(R) - σ_R) - |R|`, i.e. four times `No(R)`. -/
  remainderNetChargeQuarter : Int
  remainderNetChargeQuarterExact :
    remainderNetChargeQuarter =
      4 * (((p13RemainderCurvatureProfile
            (Node21Context active.previous)).positiveDeficiency : Int) -
          (Graph.InducedPathWindowLedger.remainderSurplus
            (Node21Context active.previous).G.object : Int)) -
        ((p13RemainderVertices
          (Node21Context active.previous)).card : Int)
  localWork : 0 = 0 := rfl

/-- Node [58]'s successor payload, indexed by the exact node-[57] predecessor
selected by Core. -/
abbrev Node58Next {V : Type u} {residual : InitialResidual V}
    (node57 : Node57Stage residual) : Type (u + 2) :=
  match node57 with
  | ⟨.bypass _, _⟩ => PUnit
  | ⟨.degraded data node56, node57Output⟩ =>
      Node58Output data.data node56 node57Output
  | ⟨.alternate data _ node56, node57Output⟩ =>
      Node58Output data.data node56 node57Output

/-- The complete carrier after node [58]. -/
abbrev Node58Stage {V : Type u} (residual : InitialResidual V) :=
  Core.ResidualRefinement.State.DependentSuccessor
    (@Node57Stage V)
    (fun _residual node57 => Node58Next node57)
    residual

/-- Framework-owned successor `[57] -> [58]`. -/
noncomputable def node58P13NetCharge {V : Type u} {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available (@Node57Stage V)) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      (@Node58Stage V) :=
  Core.ResidualRefinement.State.StageNode.mapStage
    (Previous := @Node57Stage V)
    (Next := fun _residual node57 => Node58Next node57)
    fun _residual node57 =>
      match node57 with
      | ⟨.bypass _, _⟩ => PUnit.unit
      | ⟨.degraded _data _node56, _node57Output⟩ =>
          { remainderNetChargeQuarter :=
              _node57Output.remainderNetChargeQuarter
            remainderNetChargeQuarterExact :=
              _node57Output.remainderNetChargeQuarterExact
            localWork := rfl }
      | ⟨.alternate _data _ _node56, _node57Output⟩ =>
          { remainderNetChargeQuarter :=
              _node57Output.remainderNetChargeQuarter
            remainderNetChargeQuarterExact :=
              _node57Output.remainderNetChargeQuarterExact
            localWork := rfl }

noncomputable def runInitialThroughNode58 {V : Type u}
    (residual : InitialResidual V) :=
  (runInitialThroughNode57 residual).mapYesStage
    node58P13NetCharge

def node58LocalChecks : Nat := 0

theorem node58LocalChecks_eq_zero : node58LocalChecks = 0 := rfl

end Erdos64EG.Internal
