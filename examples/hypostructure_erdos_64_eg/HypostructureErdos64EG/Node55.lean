import HypostructureErdos64EG.Node54

namespace HypostructureErdos64EG

open Hypostructure

universe u v w

structure Node55ResidualContract (Previous : Type u) (Residual : Previous -> Type v) where
  residual : ∀ previous, Residual previous

noncomputable def node55Residual
    (contract : Node53Contract Previous)
    (Terminal : Node53Stage contract -> Type v)
    (Residual : Node54Stage contract Terminal -> Type w)
    (certificate : Node55ResidualContract
      (Node54Stage contract Terminal) Residual)
    (previous : Node54Stage contract Terminal) :
    Core.Residual.Ledger.Extension (Node54Stage contract Terminal) Residual :=
  Core.Residual.Ledger.extend previous (certificate.residual previous)

abbrev Node55Stage (contract : Node53Contract Previous)
    (Terminal : Node53Stage contract -> Type v)
    (ResidualC : Node54Stage contract Terminal -> Type w) :=
  Core.Residual.Ledger.Extension (Node54Stage contract Terminal) ResidualC

noncomputable def node55 (contract : Node53Contract Previous)
    (Terminal : Node53Stage contract -> Type v)
    (ResidualC : Node54Stage contract Terminal -> Type w)
    (previous : Node54Stage contract Terminal) (residualC : ResidualC previous) :
    Node55Stage contract Terminal ResidualC :=
  Core.Residual.Ledger.extend previous residualC

end HypostructureErdos64EG
