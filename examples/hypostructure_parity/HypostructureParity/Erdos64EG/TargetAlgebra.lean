import Erdos64EG.TargetAlgebra
import HypostructureErdos64EG.TargetAlgebra

namespace HypostructureParity.Erdos64EG

/-!
# Executable target-algebra parity

The predicate comparisons pass through each package's public unbounded
characterization. They therefore compare mathematical behavior rather than
the private shape of the bounded witnesses.
-/

/-- Both executable power-of-two predicates recognize exactly the same
natural numbers. -/
theorem powerOfTwoLength_iff (length : Nat) :
    _root_.Erdos64EG.Internal.PowerOfTwoLength length ↔
      HypostructureErdos64EG.PowerOfTwoLength length :=
  (_root_.Erdos64EG.Internal.powerOfTwoLength_iff length).trans
    (HypostructureErdos64EG.powerOfTwoLength_iff length).symm

/-- The two decision procedures return the same Boolean result on every
candidate cycle length. -/
theorem powerOfTwoLength_decide_eq (length : Nat) :
    decide (_root_.Erdos64EG.Internal.PowerOfTwoLength length) =
      decide (HypostructureErdos64EG.PowerOfTwoLength length) :=
  decide_eq_decide.mpr (powerOfTwoLength_iff length)

/-- Both executable Mersenne predicates recognize exactly the same natural
numbers. -/
theorem mersenneLength_iff (length : Nat) :
    _root_.Erdos64EG.Internal.MersenneLength length ↔
      HypostructureErdos64EG.MersenneLength length :=
  (_root_.Erdos64EG.Internal.mersenneLength_iff length).trans
    (HypostructureErdos64EG.mersenneLength_iff length).symm

/-- The two decision procedures return the same Boolean result on every
candidate return length. -/
theorem mersenneLength_decide_eq (length : Nat) :
    decide (_root_.Erdos64EG.Internal.MersenneLength length) =
      decide (HypostructureErdos64EG.MersenneLength length) :=
  decide_eq_decide.mpr (mersenneLength_iff length)

#print axioms powerOfTwoLength_iff
#print axioms powerOfTwoLength_decide_eq
#print axioms mersenneLength_iff
#print axioms mersenneLength_decide_eq

end HypostructureParity.Erdos64EG
