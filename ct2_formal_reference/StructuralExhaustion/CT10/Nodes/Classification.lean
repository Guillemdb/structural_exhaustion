import StructuralExhaustion.CT10.Types
namespace StructuralExhaustion.CT10.Nodes.Classification
inductive Decision (F : Framework) (input : Input F) (labels : LabelState F input) where
  | close (certificate : C5Certificate F input labels)
  | direct (state : DirectState F input labels)
  | missing (state : MissingState F input labels)
abbrev Contract (F : Framework) (input : Input F) (labels : LabelState F input) :=
  Decision F input labels
structure Plan (F : Framework) (input : Input F) where
  decide : ∀ labels, Contract F input labels
def run {F : Framework} {input : Input F} (plan : Plan F input)
    (labels : LabelState F input) : Contract F input labels := plan.decide labels
end StructuralExhaustion.CT10.Nodes.Classification
