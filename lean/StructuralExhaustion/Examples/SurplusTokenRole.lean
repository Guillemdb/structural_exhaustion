import StructuralExhaustion.Graph.SurplusTokenRole

namespace StructuralExhaustion.Examples.SurplusTokenRole

open StructuralExhaustion.Graph

/-- A non-Erdos transfer check: the same finite role API labels a six-colour
classroom exercise with six observation kinds. -/
example : SurplusTokenRole.roleEnum.card = 36 :=
  SurplusTokenRole.role_card

example : SurplusTokenRole.pairRouteRoleEnum.card = 5 :=
  SurplusTokenRole.pairRouteRole_card

example : SurplusTokenRole.totalRoleEnum.card = 25 :=
  SurplusTokenRole.totalRole_card

example :
    (SurplusTokenRole.tokenSubtypes.filter fun subtype =>
      subtype.tokenClass = .primitive).length = 3 :=
  SurplusTokenRole.subtype_class_counts.2.2

end StructuralExhaustion.Examples.SurplusTokenRole
