import StructuralExhaustion.CT11.Types
namespace StructuralExhaustion.CT11.Nodes.Routing
inductive Decision (F : Framework) (input : Input F)
    {decomposition : DecompositionState F input}
    {admissible : AdmissibleState F input decomposition}
    (localized : LocalizationState F input admissible) where
  | toCT1 (payload : CT1Payload F input localized)
  | toCT7 (payload : CT7Payload F input localized)
  | toCT14 (payload : CT14Payload F input localized)
abbrev Contract (F : Framework) (input : Input F)
    {decomposition : DecompositionState F input}
    {admissible : AdmissibleState F input decomposition}
    (localized : LocalizationState F input admissible) := Decision F input localized
structure Plan (F : Framework) (input : Input F) where
  route : ∀ {decomposition} {admissible : AdmissibleState F input decomposition}
    (localized : LocalizationState F input admissible), Contract F input localized
def run {F : Framework} {input : Input F} (plan : Plan F input)
    {decomposition : DecompositionState F input}
    {admissible : AdmissibleState F input decomposition}
    (localized : LocalizationState F input admissible) : Contract F input localized :=
  plan.route localized
end StructuralExhaustion.CT11.Nodes.Routing
