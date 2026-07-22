import HypostructureErdos64EG.Node35

namespace HypostructureErdos64EG

open Hypostructure

universe u v w

structure Node36DecisionContract (Previous : Type u) where
  universal : Previous -> Prop
  decidable : DecidablePred universal

abbrev Node36DecisionStage (contract : Node36DecisionContract Previous) :=
  Core.Residual.Decision.Stage contract.universal
    (fun previous => ¬ contract.universal previous)

noncomputable def node36Decision (contract : Node36DecisionContract Previous)
    (previous : Previous) : Node36DecisionStage contract :=
  Core.Residual.Decision.Node.create contract.decidable
    (fun _ absent => absent) |>.run previous

structure Node36Contract (Circuit : Type u) where
  audit : Circuit -> Core.OrderThresholdSplit.Profile Bool

abbrev Node36Stage (contract : Node32Contract Previous)
    (Circuit : Node32Stage contract -> Type u)
    (Audit : Node35Stage contract Circuit -> Type v) :=
  Core.Residual.Ledger.Extension (Node35Stage contract Circuit) Audit

noncomputable def node36 (contract : Node32Contract Previous)
    (Circuit : Node32Stage contract -> Type u)
    (Audit : Node35Stage contract Circuit -> Type v)
    (previous : Node35Stage contract Circuit) (audit : Audit previous) :
    Node36Stage contract Circuit Audit :=
  Core.Residual.Ledger.extend previous audit

end HypostructureErdos64EG
