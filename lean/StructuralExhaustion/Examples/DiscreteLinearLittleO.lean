import StructuralExhaustion.Core.DiscreteLinearLittleO

namespace StructuralExhaustion.Examples.DiscreteLinearLittleO

open Filter Asymptotics
open StructuralExhaustion.Core.DiscreteLinearLittleO

example : (fun n : Nat => (7 : ℝ) * n) =o[atTop]
    (fun n : Nat => (n : ℝ) * Real.log (n : ℝ)) :=
  const_mul_natCast_isLittleO_natCast_mul_log 7

end StructuralExhaustion.Examples.DiscreteLinearLittleO
