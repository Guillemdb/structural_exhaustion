import StructuralExhaustion.CT11.Types
namespace StructuralExhaustion.CT11.Nodes.Localization
abbrev Contract (F : Framework) (input : Input F)
    {decomposition : DecompositionState F input}
    (admissible : AdmissibleState F input decomposition) :=
  LocalizationState F input admissible
structure Plan (F : Framework) (input : Input F) where
  certify : ∀ {decomposition} (admissible : AdmissibleState F input decomposition),
    Contract F input admissible
def run {F : Framework} {input : Input F} (plan : Plan F input)
    {decomposition : DecompositionState F input}
    (admissible : AdmissibleState F input decomposition) : Contract F input admissible :=
  plan.certify admissible
end StructuralExhaustion.CT11.Nodes.Localization
