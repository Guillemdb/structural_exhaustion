import HypostructureErdos64EG.InitialResidual

/-!
# Diagram node 1: theorem-root graph

Node 1 is the sole application root.  It adds no mathematical premise and is
the only EG node allowed to initialize a residual ledger.
-/

namespace HypostructureErdos64EG

universe u

/-- Exact framework stage at diagram node 1. -/
abbrev Node1Stage := InitialStage.{u}

/-- Seed node 1 from the official graph and minimum-degree hypothesis. -/
def node1 (residual : InitialResidual.{u}) : Node1Stage.{u} :=
  initialStage residual

@[simp] theorem node1_residual (residual : InitialResidual.{u}) :
    Hypostructure.Core.Residual.residualOf (node1 residual) = residual :=
  rfl

end HypostructureErdos64EG
