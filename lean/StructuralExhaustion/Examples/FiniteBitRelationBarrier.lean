import StructuralExhaustion.Core.FiniteBitRelationBarrier

namespace StructuralExhaustion.Examples.FiniteBitRelationBarrier

open StructuralExhaustion

/-- A two-label transfer check: length one is the identity relation and
length two is the complete relation. -/
def profile : Core.FiniteBitRelationBarrier.Profile 2 where
  row
    | 1, source => if source.1 = 0 then 0b01#2 else 0b10#2
    | _, _ => 0b11#2

def completeProfile : Core.FiniteBitRelationBarrier.Profile 2 where
  row _ _ := 0b11#2

def relation (_length : Nat) (_source _target : Fin 2) : Bool := true

def semanticCertificate :
    Core.FiniteBitRelationBarrier.SemanticCertificate
      completeProfile Nat id relation where
  rowExact length source := by
    change 0b11#2 = BitVec.ofFnLE (fun _ : Fin 2 => true)
    native_decide

example (length : Nat) (source target : Fin 2) :
    (completeProfile.row length source).getLsb target = relation length source target :=
  semanticCertificate.getLsb_eq length source target

def countCertificate :
    Core.FiniteBitRelationBarrier.CountCertificate profile (Fin 1) where
  leftLength _ := 1
  rightLength _ := 1
  storedSafe _ := 2
  storedFlat _ := 2
  safeExact _ := by native_decide
  flatExact _ := by native_decide

example : profile.safeCount 1 1 = 2 := by native_decide

example : profile.flatCount 1 1 = 2 := by native_decide

example : profile.obstructedCount 1 1 = 0 := by native_decide

example : profile.checks 1 1 ≤ 2 * (2 + 1) ^ 2 :=
  profile.checks_quadratic 1 1

end StructuralExhaustion.Examples.FiniteBitRelationBarrier
