import StructuralExhaustion.CT1.Types

namespace StructuralExhaustion.CT1.Nodes.Entry

abbrev Contract (F : Framework) := Input F

def run {F : Framework} (input : Input F) : Contract F := input

@[simp] theorem run_eq {F : Framework} (input : Input F) :
    run input = input := rfl

end StructuralExhaustion.CT1.Nodes.Entry
