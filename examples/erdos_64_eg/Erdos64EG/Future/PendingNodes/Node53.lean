import Erdos64EG.Future.PendingNodes.Node52
import Erdos64EG.Shared.CT15BaselineSpineDemand

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Diagram node [53]: remaining non-curvature budget

Node [53] acts only on node [50]'s literal low-entropy constructor.  The
node-[52] high output and every earlier bypass remain in the same framework
ledger.  The application supplies the four scalar quantities printed in the
paper; Core owns the exhaustive ordered split and every branch transport.
-/

/-- Exact labelled-skeleton bit capacity on the fixed vertex set. -/
noncomputable def node53SkeletonBits {V : Type u}
    {residual : InitialResidual V} (active : Node50Active V residual) : ℝ :=
  Real.logb 2 (baselineSpineStateCount (Node21Context active.previous))

/-- Exact window demand already fixed by the node-[22] normalization. -/
noncomputable def node53WindowBits {V : Type u}
    {residual : InitialResidual V} (active : Node50Active V residual) : ℝ :=
  ((node22WindowRateNumerator : ℝ) / 1000000000) *
    node22PackingCount active.previous *
      Real.logb 2
        (Node21Context active.previous).G.object.input.vertices.card

/-- Node [49]'s exact symbolic remainder-family bit count. -/
noncomputable def node53RemainderBits {V : Type u}
    {residual : InitialResidual V} (active : Node50Active V residual) : ℝ :=
  Real.logb 2
    (node49RemainderGraphFamilyCount (Node21Context active.previous))

/-- Remaining non-curvature capacity after the two already named demands. -/
noncomputable def node53RemainingNoncurvatureBits {V : Type u}
    {residual : InitialResidual V} (active : Node50Active V residual) : ℝ :=
  node53SkeletonBits active - node53WindowBits active -
    node53RemainderBits active

/-- The forced full-rank curvature cost inherited from nodes [47]--[48]. -/
noncomputable def node53ForcedCurvatureBits {V : Type u}
    {residual : InitialResidual V} (active : Node50Active V residual) : ℝ :=
  node48CurvatureEntropyCost *
    p13CurvatureTargetRank (Node21Context active.previous)

/-- Yes edge `[53] -> [54]`. -/
abbrev Node53Small {V : Type u} (residual : InitialResidual V)
    (active : Node50Active V residual)
    (_low : Node50Low residual active) : Prop :=
  node53RemainingNoncurvatureBits active <
    node53ForcedCurvatureBits active

/-- No edge `[53] -> [55]`. -/
abbrev Node53Large {V : Type u} (residual : InitialResidual V)
    (active : Node50Active V residual)
    (_low : Node50Low residual active) : Prop :=
  node53ForcedCurvatureBits active ≤
    node53RemainingNoncurvatureBits active

/-- The exact four-leaf Part-IV carrier after the node-[53] diamond. -/
abbrev Node53Stage {V : Type u} (residual : InitialResidual V) :=
  Core.ResidualRefinement.State.FocusedBranchYesContinuationNoDecision
    (Node50Bypass V) (Node50Active V)
    (@Node50High V) (@Node50Low V)
    (fun residual active high =>
      Node52Output (residual := residual) active high)
    (@Node53Small V) (@Node53Large V) residual

/-- Framework-owned exhaustive decision on node [50]'s exact low leaf. -/
noncomputable def node53P13RemainingBudgetDecision {V : Type u} {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available (@Node52Stage V)) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      (@Node53Stage V) :=
  Core.ResidualRefinement.State.StageNode.decideFocusedBranchYesContinuationNo
      (fun _residual active low => Classical.propDecidable
        (Node53Small _ active low))
      (fun _residual _active _low absent => le_of_not_gt absent)

noncomputable def runInitialThroughNode53 {V : Type u}
    (quietBlock : Node23DenseWindowQuietBlockInput V)
    (node48Input : Node48TypedYellowInput V)
    (node52Input : Node52JointAccountingTypedYellowInput V)
    (residual : InitialResidual V) :=
  (runInitialThroughNode52 quietBlock node48Input
    node52Input residual).mapYesStage node53P13RemainingBudgetDecision

/-- One proof-level ordered comparison and no finite local scan. -/
def node53LocalChecks : Nat := 0

theorem node53LocalChecks_eq_zero : node53LocalChecks = 0 := rfl

#print axioms node53P13RemainingBudgetDecision
#print axioms runInitialThroughNode53

end Erdos64EG.Internal
