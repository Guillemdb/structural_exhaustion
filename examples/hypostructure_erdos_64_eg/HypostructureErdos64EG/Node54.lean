import HypostructureErdos64EG.Node53

namespace HypostructureErdos64EG

open Hypostructure

universe u v

structure Node54GuardContract (Previous : Type u) where
  fit : Previous -> Prop
  fitDecidable : DecidablePred fit

abbrev Node54GuardStage (contract : Node54GuardContract Previous) :=
  Core.Residual.Decision.Stage contract.fit (fun previous => ¬ contract.fit previous)

noncomputable def node54Guard
    (contract : Node54GuardContract Previous) (previous : Previous) :
    Node54GuardStage contract :=
  Core.Residual.Decision.Node.create contract.fitDecidable
    (fun _ absent => absent) |>.run previous

abbrev Node54Stage (contract : Node53Contract Previous)
    (Terminal : Node53Stage contract -> Type v) :=
  Core.Residual.Ledger.Extension (Node53Stage contract) Terminal

noncomputable def node54 (contract : Node53Contract Previous)
    (Terminal : Node53Stage contract -> Type v)
    (previous : Node53Stage contract) (terminal : Terminal previous) :
    Node54Stage contract Terminal :=
  Core.Residual.Ledger.extend previous terminal

end HypostructureErdos64EG
