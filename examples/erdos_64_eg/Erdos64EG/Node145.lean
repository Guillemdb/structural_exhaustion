import Erdos64EG.Node24

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Diagram node [145]: hot/cold window interface

Node [145] consumes the surviving node-[24] residual and exposes the single
framework-owned sequential compatible-extension ledger used by the cold
branch.  It does not choose a new carrier, reorder windows, or author a
hot/cold flag: the ledger, final aggregate, original-completion witness, and
hot/cold outcome are all the accumulated values already registered by the
node-[21]/node-[24] stage entailment.
-/

/-- The exact ledger interface first made explicit at node [145].  Every
field is a projection of the accumulated sequential ledger on the identical
node-[21] packing. -/
structure Node145Output {V : Type u} {residual : InitialResidual V}
    (node18 : Node18Stage residual)
    (bounded : Node19Low residual node18)
    (node21 : Node21Output node18 bounded)
    (_low : Node22Low residual node18 bounded node21) : Type (u + 4) where
  ledger :
    P13SequentialWeightedLedger (Node21Context node18)
      node21.barrierRateCertificate
  ledgerExact :
    ledger = p13AccumulatedSequentialWindowLedger node18 bounded node21
  finalAggregate :
    P13SequentialHotAggregate (Node21Context node18)
      node21.barrierRateCertificate
  finalAggregateExact :
    finalAggregate = ledger.finalAggregate
  originalWitness :
    P13OriginalCompletionWitness finalAggregate
  hotColdOutcome :
    StructuralExhaustion.Core.SequentialCompatibleExtensionLedger.Ledger.HotColdOutcome
      ledger

/-- Node [145] is the same branch cursor as node [24], with the node-[24]
low leaf replaced by the accumulated hot/cold ledger interface. -/
abbrev Node145Stage {V : Type u} (residual : InitialResidual V) :=
  Core.ResidualRefinement.State.DependentDecisionOnNoNoAfterYes
    (@Node18Stage V) (@Node19High V) (@Node19Low V)
    (fun _residual node18 bounded => Node21Output node18 bounded)
    (@Node22High V) (@Node22Low V)
    (fun _residual node18 bounded node21 high =>
      Node23Output node18 bounded node21 high)
    (fun _residual node18 bounded node21 low =>
      Node145Output node18 bounded node21 low) residual

private noncomputable def node145Output {V : Type u}
    {residual : InitialResidual V} (node18 : Node18Stage residual)
    (bounded : Node19Low residual node18)
    (node21 : Node21Output node18 bounded)
    (low : Node22Low residual node18 bounded node21)
    (_node24 : Node24Output node18 bounded node21 low) :
    Node145Output node18 bounded node21 low := by
  let ledger := p13AccumulatedSequentialWindowLedger node18 bounded node21
  exact {
    ledger := ledger
    ledgerExact := rfl
    finalAggregate := ledger.finalAggregate
    finalAggregateExact := rfl
    originalWitness :=
      p13AccumulatedOriginalCompletionWitness node18 bounded node21
    hotColdOutcome := ledger.hotColdOutcome
  }

/-- Framework-owned `[24] -> [145]` successor.  The Erdős layer merely exposes
the accumulated sequential ledger as the first cold-branch interface. -/
noncomputable def node145P13HotColdWindowInterface {V : Type u} {facts}
    [Core.ResidualRefinement.Proofs.Contains
      (Core.ResidualRefinement.State.Available (@Node24Stage V)) facts] :
    Core.ResidualRefinement.State.StageNode (facts := facts)
      (@Node145Stage V) :=
  Core.ResidualRefinement.State.StageNode.mapDependentDecisionOnNoNoAfterYes
    (Current := fun _ node18 bounded node21 low =>
      Node24Output node18 bounded node21 low)
    (Next := fun _ node18 bounded node21 low =>
      Node145Output node18 bounded node21 low)
    fun _residual node18 bounded node21 low node24 =>
      node145Output node18 bounded node21 low node24

noncomputable def runInitialThroughNode145 {V : Type u}
    (residual : InitialResidual V) :=
  (runInitialThroughNode24 residual).mapYesStage
    node145P13HotColdWindowInterface

/-- Node [145] performs no new semantic scan; it exposes the framework ledger
already determined by the incoming residual. -/
def node145LocalChecks : Nat := 0

theorem node145LocalChecks_eq_zero : node145LocalChecks = 0 := rfl

#print axioms node145P13HotColdWindowInterface
#print axioms runInitialThroughNode145

end Erdos64EG.Internal
