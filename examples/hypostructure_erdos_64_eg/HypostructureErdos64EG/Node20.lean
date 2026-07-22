import HypostructureErdos64EG.Node19

namespace HypostructureErdos64EG

universe u

/-! Node20 is the named high branch of Node19.  It introduces no new data or
route; the decision stage itself is the framework-owned branch cursor. -/

abbrev Node20Stage (contract : Node19Contract Previous) := Node19Stage contract

abbrev Node20Entry (contract : Node19Contract Previous)
    (stage : Previous) : Prop := Node19High contract stage

theorem node20_entry_is_node19_high (contract : Node19Contract Previous)
    (stage : Previous) :
    Node20Entry contract stage ↔ Node19High contract stage := Iff.rfl

end HypostructureErdos64EG
