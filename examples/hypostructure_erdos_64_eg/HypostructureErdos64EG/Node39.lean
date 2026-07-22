import HypostructureErdos64EG.Node38

namespace HypostructureErdos64EG

universe u v

structure Node39ClosureContract (Previous : Type u) (Certificate : Previous -> Prop) where
  certificate : ∀ previous, Certificate previous
  contradiction : ∀ previous, Certificate previous -> False

theorem node39_closes
    (contract : Node39ClosureContract Previous Certificate)
    (previous : Previous) : False :=
  contract.contradiction previous (contract.certificate previous)

abbrev Node39Stage (contract : Node38Contract Previous) := Node38Stage contract
abbrev Node39Output (contract : Node38Contract Previous) : Type v := PUnit

end HypostructureErdos64EG
