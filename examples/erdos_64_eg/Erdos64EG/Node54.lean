import Erdos64EG.Node53
import StructuralExhaustion.Core.FinitePoweredBudgetTransfer
import StructuralExhaustion.Core.GracefulDegradation

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Diagram node [54]: Part-IV terminal joins

Node [54] has exactly the two terminal incoming edges in the paper's Part-IV
diamond.  The high node-[52] edge closes by direct inequality reversal.  The
small node-[53] edge closes by Core's powered-budget transfer applied to the
product-cost certificate produced at node [48] and transported through the
single accumulated ledger to node [53].
-/

/-- The literal negation of node [52]'s normalized, error-bearing joint
budget.  Node [54] consumes node [52]'s stored budget certificate; it does not
duplicate that long expression in a second consumer-side formula. -/
def Node54HighTheta {V : Type u} {residual : InitialResidual V}
    (active : Node50Active V residual) : Prop :=
  ¬ Node52JointBudget active

/-- Node [54]'s branch-local mathematical output on the literal node-[52]
leaf.  It proves only that node [52]'s exact non-strict feasibility budget
excludes its exact strict reverse. -/
structure Node54HighTerminal {V : Type u}
    {residual : InitialResidual V}
    (active : Node50Active V residual)
    (_high : Node50High residual active)
    (_node52 : Node52Output active _high) : Type (u + 2) where
  highThetaImpossible : ¬ Node54HighTheta active

/-- Kernel-level elimination of the exact two inequalities on the high
incoming edge. -/
noncomputable def node54HighTerminal {V : Type u}
    {residual : InitialResidual V} (active : Node50Active V residual)
    (high : Node50High residual active) (node52 : Node52Output active high) :
    Node54HighTerminal active high node52 :=
  ⟨not_not_intro node52.jointBudget⟩

/-- The verified high terminal performs no finite scan. -/
def node54HighLocalChecks : Nat := 0

theorem node54HighLocalChecks_eq_zero : node54HighLocalChecks = 0 := rfl

/-- Exact finite product-fit guard needed only on node [53]'s small-budget
leaf.  Its negation is retained as the curvature-unpaid degradation residual;
it is never promoted to a graph theorem or silently assumed. -/
abbrev Node54ProductFit {V : Type u} {residual : InitialResidual V}
    (active : Node50Active V residual)
    (_low : Node50Low residual active)
    (_small : Node53Small residual active _low) : Prop :=
  node53ForcedPower active ≤
    node53FlatPower active * active.output.stateCount

/-- Kernel-level elimination of the exact node-[53] small branch when its
literal product-fit guard holds. -/
noncomputable def node54SmallBudgetImpossible {V : Type u}
    {residual : InitialResidual V} (active : Node50Active V residual)
    (low : Node50Low residual active)
    (small : Node53Small residual active low)
    (fit : Node54ProductFit active low small) : False := by
  have strictLarge :
      node53ForcedPower active ^ 10 <
        node53FlatPower active ^ 10 * node53UpperPower active := by
    exact Core.FinitePoweredBudgetTransfer.forced_pow_lt_flat_pow_mul_upper
      fit low (Nat.pow_pos (by norm_num : 0 < 111286))
  exact (Nat.not_le_of_lt strictLarge) small

/-- After node [54], Core retains exactly two live reasons on the same active
residual: failed product fit on the small-budget leaf, or the paper's original
node-[53] large-budget leaf. -/
abbrev Node54Stage {V : Type u} (residual : InitialResidual V) :=
  Core.ResidualRefinement.State.GuardedDegradation
    (Node50Bypass V) (Node50Active V) (@Node50High V) (@Node50Low V)
    (fun residual active high =>
      Node52Output (residual := residual) active high)
    (@Node53Small V) (@Node53Large V)
    (fun residual active high node52 =>
      Node54HighTerminal (residual := residual) active high node52)
    (@Node54ProductFit V) residual

/-- Framework-owned node-[54] join/closure.  Application code supplies only
the two local terminal proofs; Core owns all bypass and surviving-leaf
transport. -/
noncomputable def node54P13PartIVTerminalJoin {V : Type u} {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available (@Node53Stage V)) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      (@Node54Stage V) :=
  Core.ResidualRefinement.State.StageNode.terminalizeGuardOrDegrade
    (terminal := fun residual active high node52 =>
      node54HighTerminal (residual := residual) active high node52)
    (decideGuard := fun _residual active low small =>
      inferInstanceAs (Decidable (Node54ProductFit active low small)))
    (close := fun _residual active low small fit =>
      node54SmallBudgetImpossible active low small fit)

noncomputable def runInitialThroughNode54 {V : Type u}
    (residual : InitialResidual V) :=
  (runInitialThroughNode53 residual).mapYesStage
    node54P13PartIVTerminalJoin

/-- Node [54] adds no finite scan beyond the symbolic powered-budget
transport owned by Core. -/
def node54SmallLocalChecks : Nat := 0

theorem node54SmallLocalChecks_eq_zero : node54SmallLocalChecks = 0 := rfl

#print axioms node54HighTerminal
#print axioms node54SmallBudgetImpossible
#print axioms node54P13PartIVTerminalJoin
#print axioms runInitialThroughNode54

end Erdos64EG.Internal
