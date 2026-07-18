import StructuralExhaustion.Core.ExactHandoff

namespace StructuralExhaustion.Examples.ExactHandoff

open StructuralExhaustion

def incoming : Nat := 7

def retained : Core.ExactHandoff incoming := Core.ExactHandoff.refl incoming

example : retained.previous = incoming := retained.previous_eq

example : retained.previous + 1 = 8 :=
  retained.property (fun value => value + 1 = 8) (by decide)

end StructuralExhaustion.Examples.ExactHandoff
