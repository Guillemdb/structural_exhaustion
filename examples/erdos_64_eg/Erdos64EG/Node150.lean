import Erdos64EG.Node148

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Diagram node [150]: cold residual after live-hot cap failure

Node [150] consumes only the no edge of node [148].  It records the exact
failed-cap residual and the cold ledger visible from the same node-[21]
barrier certificate.  The stronger cold-mass lower bound depends on the
separate hot-payment normalization producer; since that fact is not available
on the current direct accumulated chain, it is retained as an explicit
residual requirement rather than assumed.
-/

noncomputable def node150ColdCount {V : Type u}
    {residual : InitialResidual V} (active : Node148Active V residual) : Nat :=
  (p13SequentialWeightedColdWindows (Node21Context active.node18)
    active.node21.barrierRateCertificate).length

/-- Obligations that remain after the current framework-native node-[150]
residual.  These are requirement labels, not assumptions. -/
inductive Node150Requirement
  | hotPaymentProducer
  | coldMassLowerBound
  deriving DecidableEq, Repr

def node150Requirements : List Node150Requirement :=
  [.hotPaymentProducer, .coldMassLowerBound]

theorem node150Requirements_nodup : node150Requirements.Nodup := by
  decide

/-- The dependency-ready node-[150] residual on the exact node-[148] no edge. -/
structure Node150ColdResidual {V : Type u} {residual : InitialResidual V}
    (active : Node148Active V residual)
    (_node148No : Node148To150 active) : Type (u + 3) where
  failedCap : Node148LiveHotFailure active
  lowerThreshold :
    (Node21Context active.node18).G.object.input.vertices.card ≤
      78 * p13 (Node21Context active.node18)
  coldCount : Nat
  coldCountExact : coldCount = node150ColdCount active
  totalDemandExact :
    node148TotalDemand active =
      node148HotDemand active + node148ColdDemand active
  unpaidTotal :
    node148Allowance active < node148TotalDemand active
  requirements : List Node150Requirement
  requirementsExact : requirements = node150Requirements
  requirementsNodup : requirements.Nodup

abbrev Node150Stage {V : Type u} (residual : InitialResidual V) :=
  Core.ResidualRefinement.State.FocusedBranchDecisionNoContinuation
    (Node148Bypass V) (Node148Active V)
    (@Node148LiveHotCap V) (@Node148LiveHotFailure V)
    (fun residual active failed =>
      Node150ColdResidual (residual := residual) active
        (Node148To150.mk failed active.output.crossMultiplied
          (node148_totalDemand_eq_hot_add_cold active)))
    residual

noncomputable def node150ColdResidual {V : Type u} {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available (@Node148To150Stage V)) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      (@Node150Stage V) :=
  Core.ResidualRefinement.State.StageNode.mapFocusedBranchNoContinuation
    fun _residual active _failed (node148No : Node148To150 active) =>
      { failedCap := node148No.failedCap
        lowerThreshold := node148No.lowerThreshold
        coldCount := node150ColdCount active
        coldCountExact := rfl
        totalDemandExact := node148No.totalDemandExact
        unpaidTotal := Nat.lt_of_not_ge node148No.failedCap
        requirements := node150Requirements
        requirementsExact := rfl
        requirementsNodup := node150Requirements_nodup }

noncomputable def runInitialThroughNode150 {V : Type u}
    (residual : InitialResidual V) :=
  (runInitialThroughNode148To150 residual).mapYesStage
    node150ColdResidual

def node150LocalChecks : Nat := 0

theorem node150LocalChecks_eq_zero : node150LocalChecks = 0 := rfl

#print axioms node150ColdResidual
#print axioms runInitialThroughNode150

end Erdos64EG.Internal
