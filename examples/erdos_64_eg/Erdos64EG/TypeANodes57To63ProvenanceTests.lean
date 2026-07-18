import Erdos64EG.TypeANodes57To63Provenance

namespace Erdos64EG.Internal.TypeANodes57To63Provenance

open StructuralExhaustion

universe u

variable {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
variable {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}

noncomputable example (node24 : VerifiedP13WindowDensityOutput ctx node21) :=
  let source57 := node57 node24
  let source58 := node58 source57
  let source59 := node59 source58
  let source61 := node61 source59
  node62 source61

example (node24 : VerifiedP13WindowDensityOutput ctx node21) :
    (node57 node24).previous = p13ClosureRobustPartIV node24 := rfl

#print axioms node57
#print axioms node58
#print axioms node59
#print axioms node60_impossible
#print axioms node61
#print axioms node62

end Erdos64EG.Internal.TypeANodes57To63Provenance
