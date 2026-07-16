import StructuralExhaustion.Graph.FanCertificateRequirement

namespace StructuralExhaustion.Examples.FanCertificateRequirement

open StructuralExhaustion
open StructuralExhaustion.Graph

universe u

variable {V : Type u} (object : FiniteObject V) (center : V)
variable (centerHigh : 4 ≤ object.degree center)

/-- Non-Erdős transfer: the first requested label is attached to literal port
zero in the actual neighbour schedule. -/
example :
    (Graph.FanCertificateRequirement.firstLabelRequest object center
      centerHigh).port.1 = 0 :=
  Graph.FanCertificateRequirement.firstLabelRequest_port_index object center
    centerHigh

example : Graph.FanCertificateRequirement.visibleChecks = 0 :=
  Graph.FanCertificateRequirement.visibleChecks_eq_zero

end StructuralExhaustion.Examples.FanCertificateRequirement
