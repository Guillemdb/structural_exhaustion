import StructuralExhaustion.CT8.Types
namespace StructuralExhaustion.CT8.Nodes.Repetition
inductive Decision (F : Framework) (input : Input F)
    (equality : EqualityState F input) where
  | short (certificate : C5Certificate F input equality)
  | repeated (state : RepeatedState F input equality)
abbrev Contract (F : Framework) (input : Input F)
    (equality : EqualityState F input) := Decision F input equality
structure Plan (F : Framework) (input : Input F) where
  decide : ∀ equality, Contract F input equality
def run {F : Framework} {input : Input F} (plan : Plan F input)
    (equality : EqualityState F input) : Contract F input equality := plan.decide equality
end StructuralExhaustion.CT8.Nodes.Repetition
