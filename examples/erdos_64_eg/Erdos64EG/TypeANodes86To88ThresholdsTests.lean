import Erdos64EG.TypeANodes86To88Thresholds

namespace Erdos64EG.Internal.TypeANodes86To88Thresholds

open StructuralExhaustion

universe u

variable {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}

example {node61 : Node61 (ctx := ctx)} (node63 : Node63 node61) :
    (node86 (ctx := ctx) node63).previous = node63 := rfl

example {node61 : Node61 (ctx := ctx)} {node63 : Node63 node61}
    (source86 : VerifiedNode86Residual node61 node63) :
    4 * (Graph.NegativeSupportHandoff.chargeProfile ctx.G.object
      node61.support.core).positiveDeficiency < node61.support.core.card :=
  source86.four_deficiency_lt_card

example {node61 : Node61 (ctx := ctx)} {node63 : Node63 node61}
    (source86 : VerifiedNode86Residual node61 node63) :
    (node87 source86).previous = source86 ∧
      node61.support.core.card ≤ 6142 :=
  ⟨rfl, (node87 source86).supportCardAtMost6142⟩

example {node61 : Node61 (ctx := ctx)} {node63 : Node63 node61}
    {source86 : VerifiedNode86Residual node61 node63}
    (source87 : VerifiedNode87Residual source86) :
    (4 : Nat) * (0 + 1) ≤ 4 ∧
      (4 : Nat) * (1 + 1) ≤ 8 ∧
        (4 : Nat) * (2 + 1) ≤ 12 :=
  ⟨(node88 source87).H0_le_four, (node88 source87).H1_le_eight,
    (node88 source87).H2_le_twelve⟩

#print axioms node86
#print axioms node87_p13Free
#print axioms node87
#print axioms node88

end Erdos64EG.Internal.TypeANodes86To88Thresholds
