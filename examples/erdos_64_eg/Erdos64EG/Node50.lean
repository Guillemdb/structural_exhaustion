import Erdos64EG.Node49

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Diagram node [50]: high/low remainder entropy

Core focuses the sole live full-rank node-[49] leaf and owns the bypass bundle
containing the already handled non-near-cubic and rank-drop leaves.  The Erdős
instantiation supplies only the paper's exact natural-power comparison.
-/

abbrev Node50Bypass (V : Type u) :=
  Core.ResidualRefinement.State.FocusedBranchDecisionNoContinuationBypass
    (@Node32Bypass V) (@Node32Active V)
    (fun _ data => Node32RankDrop data.previous)
    (fun _ data => Node32FullRank data.previous)

abbrev Node50Active (V : Type u) :=
  Core.ResidualRefinement.State.FocusedBranchDecisionNoContinuationActive
    (@Node32Active V)
    (fun _ data => Node32FullRank data.previous)
    (fun _ data _fullRank =>
      Node49Output data.previous data.outerProof data.outerOutput)

namespace Node50Active

def previous {V : Type u} {residual : InitialResidual V}
    (active : Node50Active V residual) : Node18Stage residual :=
  active.data.previous

def node49Output {V : Type u} {residual : InitialResidual V}
    (active : Node50Active V residual) :
    Node49Output active.data.previous active.data.outerProof
      active.data.outerOutput :=
  active.output

end Node50Active

/-- Yes edge `[50] -> [51]`. -/
abbrev Node50High {V : Type u} (residual : InitialResidual V)
    (active : Node50Active V residual) : Prop :=
  (Node21Context active.previous).G.object.input.vertices.card ^
      (p13RemainderVertices (Node21Context active.previous)).card ≤
    active.output.stateCount ^ 10

/-- No edge `[50] -> [53]`. -/
abbrev Node50Low {V : Type u} (residual : InitialResidual V)
    (active : Node50Active V residual) : Prop :=
  active.output.stateCount ^ 10 <
    (Node21Context active.previous).G.object.input.vertices.card ^
      (p13RemainderVertices (Node21Context active.previous)).card

abbrev Node50Stage {V : Type u} (residual : InitialResidual V) :=
  Core.ResidualRefinement.State.FocusedBranchDecision
    (Node50Bypass V) (Node50Active V)
    (@Node50High V) (@Node50Low V) residual

/-- Framework-owned exhaustive decision on the exact node-[49] active leaf. -/
noncomputable def node50P13EntropyDecision {V : Type u} {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available (@Node49Stage V)) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      (@Node50Stage V) :=
  Core.ResidualRefinement.State.StageNode.decideFocusedBranchNoContinuation
    (fun _ active => inferInstanceAs (Decidable (Node50High _ active)))
    (fun _ _active absent => Nat.lt_of_not_ge absent)

noncomputable def runInitialThroughNode50 {V : Type u}
    (residual : InitialResidual V) :=
  (runInitialThroughNode49 residual).mapYesStage node50P13EntropyDecision

theorem node50_exhaustive {V : Type u} {residual : InitialResidual V}
    (active : Node50Active V residual) :
    Node50High residual active ∨ Node50Low residual active :=
  le_or_gt _ _

def node50LocalChecks : Nat := 0

theorem node50LocalChecks_eq_zero : node50LocalChecks = 0 := rfl

#print axioms node50P13EntropyDecision
#print axioms runInitialThroughNode50
#print axioms node50_exhaustive

end Erdos64EG.Internal
