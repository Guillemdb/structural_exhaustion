import Erdos64EG.Node146

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Diagram node [148]: live-hot entropy-cap decision

Node [148] consumes only the literal no leaf of node [146].  Core focuses that
leaf from the accumulated node-[146] no-continuation stage, preserves the
already handled route-8 yes branch, and performs the paper's live-hot cap
comparison.  The two resulting constructors are exactly the existing
diagram edges `[148] -> [149]` and `[148] -> [150]`.
-/

/-- Paper numerator for the live-hot demand coefficient at node [148]. -/
def node148LiveHotRateNumerator : Nat := 118108581006

/-- Paper skeleton numerator for the live-hot cap at node [148]. -/
def node148LiveHotSkeletonNumerator : Nat := 1500000000

abbrev Node148Bypass (V : Type u) :=
  Core.ResidualRefinement.State.FocusedBranchDecisionNoContinuationBypass
    (@Node146Bypass V) (@Node146Active V)
    (@Node146Route8BelowThreshold V) (@Node146Route8NotBelow V)

abbrev Node148Active (V : Type u) :=
  Core.ResidualRefinement.State.FocusedBranchDecisionNoContinuationActive
    (@Node146Active V) (@Node146Route8NotBelow V)
    (fun _residual active notBelow => Node146To148Marker active notBelow)

namespace Node148Active

def node18 {V : Type u} {residual : InitialResidual V}
    (active : Node148Active V residual) :
    Node18Stage residual :=
  active.data.previous

def node21 {V : Type u} {residual : InitialResidual V}
    (active : Node148Active V residual) :
    Node21Output active.data.previous active.data.outerProof :=
  active.data.outerOutput

def node146No {V : Type u} {residual : InitialResidual V}
    (active : Node148Active V residual) :
    Node146To148Marker active.data active.proof :=
  active.output

end Node148Active

noncomputable def node148TotalDemand {V : Type u}
    {residual : InitialResidual V} (active : Node148Active V residual) : Nat :=
  node148LiveHotRateNumerator * p13 (Node21Context active.node18) *
    Nat.log 2 (Node21Context active.node18).G.object.input.vertices.card

noncomputable def node148HotDemand {V : Type u}
    {residual : InitialResidual V} (active : Node148Active V residual) : Nat :=
  node148LiveHotRateNumerator *
    (p13SequentialWeightedHotWindows (Node21Context active.node18)
      active.node21.barrierRateCertificate).length *
    Nat.log 2 (Node21Context active.node18).G.object.input.vertices.card

noncomputable def node148ColdDemand {V : Type u}
    {residual : InitialResidual V} (active : Node148Active V residual) : Nat :=
  node148LiveHotRateNumerator *
    (p13SequentialWeightedColdWindows (Node21Context active.node18)
      active.node21.barrierRateCertificate).length *
    Nat.log 2 (Node21Context active.node18).G.object.input.vertices.card

noncomputable def node148Allowance {V : Type u}
    {residual : InitialResidual V} (active : Node148Active V residual) : Nat :=
  node148LiveHotSkeletonNumerator *
    (Node21Context active.node18).G.object.input.vertices.card *
    Nat.log 2 (Node21Context active.node18).G.object.input.vertices.card

/-- The exact executable predicate at node `[148]`. -/
def Node148LiveHotCap {V : Type u} {residual : InitialResidual V}
    (active : Node148Active V residual) : Prop :=
  node148TotalDemand active ≤ node148Allowance active

def Node148LiveHotFailure {V : Type u} {residual : InitialResidual V}
    (active : Node148Active V residual) : Prop :=
  ¬Node148LiveHotCap active

/-- Exact hot/cold partition of node [148]'s demand on the incoming ledger. -/
theorem node148_totalDemand_eq_hot_add_cold {V : Type u}
    {residual : InitialResidual V} (active : Node148Active V residual) :
    node148TotalDemand active =
      node148HotDemand active + node148ColdDemand active := by
  have partition := p13SequentialWeightedHotCount_add_coldCount
    (Node21Context active.node18) active.node21.barrierRateCertificate
  unfold node148TotalDemand node148HotDemand node148ColdDemand
  rw [← partition]
  ring

/-- Framework marker on the `[148] -> [149]` yes edge. -/
abbrev Node148To149Marker {V : Type u} {residual : InitialResidual V}
    (_active : Node148Active V residual)
    (_cap : Node148LiveHotCap _active) : Type (u + 3) :=
  PUnit

/-- Framework marker on the `[148] -> [150]` no edge. -/
abbrev Node148To150Marker {V : Type u} {residual : InitialResidual V}
    (_active : Node148Active V residual)
    (_failed : Node148LiveHotFailure _active) : Type (u + 3) :=
  PUnit

abbrev Node148DecisionStage {V : Type u} (residual : InitialResidual V) :=
  Core.ResidualRefinement.State.FocusedBranchDecision
    (Node148Bypass V) (Node148Active V)
    (@Node148LiveHotCap V) (@Node148LiveHotFailure V) residual

abbrev Node148To149Stage {V : Type u} (residual : InitialResidual V) :=
  Core.ResidualRefinement.State.FocusedBranchDecisionYesContinuation
    (Node148Bypass V) (Node148Active V)
    (@Node148LiveHotCap V) (@Node148LiveHotFailure V)
    (fun _residual active cap => Node148To149Marker active cap) residual

abbrev Node148To150Stage {V : Type u} (residual : InitialResidual V) :=
  Core.ResidualRefinement.State.FocusedBranchDecisionNoContinuation
    (Node148Bypass V) (Node148Active V)
    (@Node148LiveHotCap V) (@Node148LiveHotFailure V)
    (fun _residual active failed => Node148To150Marker active failed) residual

/-- Framework-owned exhaustive cap decision on the literal node-[146] no
leaf. -/
noncomputable def node148LiveHotCapDecision {V : Type u} {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available (@Node146To148Stage V)) facts] :
  Core.ResidualRefinement.State.StageNode (facts := facts)
      (@Node148DecisionStage V) :=
  Core.ResidualRefinement.State.StageNode.decideFocusedBranchNoContinuation
    (fun _ active => Classical.propDecidable (Node148LiveHotCap active))
    (fun _ _active absent => absent)

noncomputable def node148To149Refinement {V : Type u} {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available (@Node148DecisionStage V)) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      (@Node148To149Stage V) :=
  Core.ResidualRefinement.State.StageNode.continueFocusedBranchYes
    fun _residual _active _cap => PUnit.unit

noncomputable def node148To150Refinement {V : Type u} {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available (@Node148DecisionStage V)) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      (@Node148To150Stage V) :=
  Core.ResidualRefinement.State.StageNode.continueFocusedBranchNo
    fun _residual _active _failed => PUnit.unit

noncomputable def runInitialThroughNode148Decision {V : Type u}
    (residual : InitialResidual V) :=
  (runInitialThroughNode146To148 residual).mapYesStage
    node148LiveHotCapDecision

noncomputable def runInitialThroughNode148To149 {V : Type u}
    (residual : InitialResidual V) :=
  (runInitialThroughNode148Decision residual).mapYesStage
    node148To149Refinement

noncomputable def runInitialThroughNode148To150 {V : Type u}
    (residual : InitialResidual V) :=
  (runInitialThroughNode148Decision residual).mapYesStage
    node148To150Refinement

/-- Node [148] performs one primitive arithmetic comparison. -/
def node148LocalChecks : Nat := 1

theorem node148LocalChecks_eq_one : node148LocalChecks = 1 := rfl

#print axioms node148LiveHotCapDecision
#print axioms node148To149Refinement
#print axioms node148To150Refinement
#print axioms runInitialThroughNode148To149
#print axioms runInitialThroughNode148To150

end Erdos64EG.Internal
