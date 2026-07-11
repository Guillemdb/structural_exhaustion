import StructuralExhaustion.CT2.Types

namespace StructuralExhaustion.CT2.Nodes.Entry

/-- Validated input is the entry-node contract. -/
abbrev Contract (F : Framework) := Input F

def run {F : Framework} (input : Input F) : Contract F := input

@[simp] theorem run_eq {F : Framework} (input : Input F) :
    run input = input := rfl

end StructuralExhaustion.CT2.Nodes.Entry
