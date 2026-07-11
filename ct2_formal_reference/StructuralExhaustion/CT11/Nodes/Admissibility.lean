import StructuralExhaustion.CT11.Types
namespace StructuralExhaustion.CT11.Nodes.Admissibility
inductive Decision (F : Framework) (input : Input F)
    (decomposition : DecompositionState F input) where
  | refine (payload : CT10Payload F input decomposition)
  | closed (state : AdmissibleState F input decomposition)
abbrev Contract (F : Framework) (input : Input F)
    (decomposition : DecompositionState F input) := Decision F input decomposition
structure Plan (F : Framework) (input : Input F) where
  decide : ∀ decomposition, Contract F input decomposition
def run {F : Framework} {input : Input F} (plan : Plan F input)
    (decomposition : DecompositionState F input) : Contract F input decomposition :=
  plan.decide decomposition
end StructuralExhaustion.CT11.Nodes.Admissibility
