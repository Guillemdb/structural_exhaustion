import HypostructureErdos64EG.Node22

namespace HypostructureErdos64EG

open Hypostructure

universe u w x

abbrev Node23Stage (contract : Node22Contract Previous Table Index) := Node22Stage contract

abbrev Node23Entry (contract : Node22Contract Previous Table Index)
    (stage : Node21Stage contract.base Table Index) : Prop :=
  Node22High contract stage

theorem node23_entry_is_node22_high (contract : Node22Contract Previous Table Index)
    (stage : Node21Stage contract.base Table Index) :
    Node23Entry contract stage ↔ Node22High contract stage := Iff.rfl

end HypostructureErdos64EG
