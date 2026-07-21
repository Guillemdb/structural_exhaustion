import Erdos64EG.Node54

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Diagram node [55]: large-budget residual C

Node [55] names exactly the surviving `[53] no` leaf after node [54] has
terminalized the other two Part-IV leaves.  The output records only the
paper-local large-budget residual data: the inherited window-density cap and
the strict large-budget constructor.  Core owns the focused-leaf transport.
-/

/-- The literal live Part-IV residual after node [54]. -/
abbrev Node55Active (V : Type u) :=
  Core.ResidualRefinement.State.FocusedBranchNestedNoActive
    (Node50Active V) (@Node50Low V) (@Node53Large V)

/-- Only the local data first named at node [55]. -/
structure Node55Output {V : Type u} {residual : InitialResidual V}
    (active : Node55Active V residual) : Type (u + 2) where
  windowDensity :
    Node22Low residual active.data.previous active.data.data.outerProof
      active.data.data.outerOutput
  largeBudget : Node53Large residual active.data active.outerProof
  localWork : 0 = 0 := rfl

/-- The complete Part-IV carrier after node [55]. -/
abbrev Node55Stage {V : Type u} (residual : InitialResidual V) :=
  Core.ResidualRefinement.State.GuardedDegradationAlternateContinuation
    (Node50Bypass V) (Node50Active V) (@Node50High V) (@Node50Low V)
    (fun residual active high =>
      Node52Output (residual := residual) active high)
    (@Node53Small V) (@Node53Large V)
    (fun residual active high node52 =>
      Node54HighTerminal (residual := residual) active high node52)
    (@Node54ProductFit V)
    (fun _residual active => Node55Output active) residual

/-- Framework-owned continuation of the sole live node-[54] residual. -/
noncomputable def node55P13LargeBudgetResidual {V : Type u} {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available (@Node54Stage V)) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      (@Node55Stage V) :=
  Core.ResidualRefinement.State.StageNode.continueGuardedDegradationAlternate
    fun _residual active => {
      windowDensity := by
        exact active.data.data.innerProof
      largeBudget := active.innerProof
      localWork := rfl
    }

noncomputable def runInitialThroughNode55 {V : Type u}
    (residual : InitialResidual V) :=
  (runInitialThroughNode54 residual).mapYesStage
    node55P13LargeBudgetResidual

def node55LocalChecks : Nat := 0

theorem node55LocalChecks_eq_zero : node55LocalChecks = 0 := rfl

#print axioms node55P13LargeBudgetResidual
#print axioms runInitialThroughNode55

end Erdos64EG.Internal
