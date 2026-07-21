import Erdos64EG.Node24

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Diagram node [145]: hot/cold window interface

Node [145] consumes the surviving node-[24] residual and advances the branch
cursor to the hot/cold interface.  The sequential compatible-extension ledger
remains available from its framework ledger producer; this node does not copy
it into an Erdős-owned output record.
-/

/-- Node [145] is the same branch cursor as node [24], with the node-[24]
low leaf advanced by a framework-owned unit payload. -/
abbrev Node145Marker {V : Type u} {residual : InitialResidual V}
    (_node18 : Node18Stage residual)
    (_bounded : Node19Low residual _node18)
    (_node21 : Node21Output _node18 _bounded)
    (_low : Node22Low residual _node18 _bounded _node21) : Type (u + 3) :=
  PUnit

abbrev Node145Stage {V : Type u} (residual : InitialResidual V) :=
  Core.ResidualRefinement.State.DependentDecisionOnNoNoAfterYes
    (@Node18Stage V) (@Node19High V) (@Node19Low V)
    (fun _residual node18 bounded => Node21Output node18 bounded)
    (@Node22High V) (@Node22Low V)
    (fun _residual node18 bounded node21 high =>
      Node23Output node18 bounded node21 high)
    (fun _residual node18 bounded node21 low =>
      Node145Marker node18 bounded node21 low) residual

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
      Node145Marker node18 bounded node21 low)
    fun _residual _node18 _bounded _node21 _low _node24 => PUnit.unit

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
