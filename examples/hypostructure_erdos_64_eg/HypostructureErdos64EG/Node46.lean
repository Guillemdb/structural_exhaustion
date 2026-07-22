import HypostructureErdos64EG.Node45

namespace HypostructureErdos64EG

universe u v w x

structure Node46ClosureContract (Previous : Type u) (Evidence : Previous -> Prop) where
  evidence : ∀ previous, Evidence previous
  contradiction : ∀ previous, Evidence previous -> False

theorem node46_close
    (contract : Node46ClosureContract Previous Evidence) (previous : Previous) : False :=
  contract.contradiction previous (contract.evidence previous)

abbrev Node46Stage (contract : Node41Contract Previous)
    (Fact : Node41Stage contract -> Type v)
    (Repair : Node43Stage contract Fact -> Type w)
    (Barrier : Node44Stage contract Fact Repair -> Type x) :=
  Node45Stage contract Fact Repair Barrier

end HypostructureErdos64EG
