import Mathlib.Data.BitVec
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic
import Hypostructure.Core.Budget.Work

/-!
# Finite bit-relation barrier counts

This module is domain-neutral.  A profile is a length-indexed family of Boolean
relations on a finite label carrier, represented by bit rows.  The framework
derives safe two-leg counts, composed-flat counts, complementary obstruction
counts, and a quadratic work envelope.
-/

namespace Hypostructure.Core.FiniteBitRelationBarrier

open scoped BigOperators

/-- A length-indexed family of Boolean relation rows on `size` labels. -/
structure Profile (size : Nat) where
  row : Nat -> Fin size -> BitVec size

namespace Profile

variable {size : Nat} (profile : Profile size)

/-- Number of compatible two-leg triples, summed by the middle label. -/
def safeCount (leftLength rightLength : Nat) : Nat :=
  ∑ middle : Fin size,
    (profile.row leftLength middle).cpop.toNat *
      (profile.row rightLength middle).cpop.toNat

/-- Number of two-leg triples whose composed leg is also compatible. -/
def flatCount (leftLength rightLength : Nat) : Nat :=
  ∑ source : Fin size, ∑ middle : Fin size,
    if (profile.row leftLength source).getLsb middle then
      (((profile.row rightLength middle) &&&
        (profile.row (leftLength + rightLength) source)).cpop).toNat
    else 0

/-- Complementary, composition-obstructed triple count. -/
def obstructedCount (leftLength rightLength : Nat) : Nat :=
  profile.safeCount leftLength rightLength -
    profile.flatCount leftLength rightLength

theorem obstructed_add_flat
    (leftLength rightLength : Nat)
    (flat_le : profile.flatCount leftLength rightLength <=
      profile.safeCount leftLength rightLength) :
    profile.obstructedCount leftLength rightLength +
        profile.flatCount leftLength rightLength =
      profile.safeCount leftLength rightLength :=
  Nat.sub_add_cancel flat_le

/-- Primitive bit operations used by one relation-barrier count. -/
def checks (_profile : Profile size) (_leftLength _rightLength : Nat) : Nat :=
  size + size ^ 2

theorem checks_quadratic (leftLength rightLength : Nat) :
    profile.checks leftLength rightLength <= 2 * (size + 1) ^ 2 := by
  simp only [checks]
  nlinarith [Nat.zero_le size]

def workBudget : _root_.Hypostructure.Core.PolynomialCheckBudget
    (Nat × Nat) where
  size := fun _ => size
  checks := fun lengths => profile.checks lengths.1 lengths.2
  coefficient := 2
  degree := 2
  bounded := by
    intro lengths
    exact profile.checks_quadratic lengths.1 lengths.2

end Profile

/-- Pack a decidable relation row into the bit representation used by the
barrier counters. -/
def semanticRow {size : Nat}
    (relation : Fin size -> Fin size -> Bool) (source : Fin size) :
    BitVec size :=
  BitVec.ofFnLE (relation source)

@[simp] theorem semanticRow_getLsb {size : Nat}
    (relation : Fin size -> Fin size -> Bool)
    (source target : Fin size) :
    (semanticRow relation source).getLsb target = relation source target :=
  BitVec.getLsb_ofFnLE _ _

/-- A semantic audit for one length-indexed relation table. -/
structure SemanticCertificate {size : Nat} (profile : Profile size)
    (Length : Type*) (lengthValue : Length -> Nat)
    (relation : Length -> Fin size -> Fin size -> Bool) : Prop where
  row_semantic : forall length source target,
    (profile.row (lengthValue length) source).getLsb target =
      relation length source target

/-- Stored count columns for a selected finite index family. -/
structure CountCertificate {size : Nat} (profile : Profile size)
    (Index : Type*) where
  leftLength : Index -> Nat
  rightLength : Index -> Nat
  storedSafe : Index -> Nat
  storedFlat : Index -> Nat
  safeExact : forall index,
    storedSafe index = profile.safeCount (leftLength index) (rightLength index)
  flatExact : forall index,
    storedFlat index = profile.flatCount (leftLength index) (rightLength index)

/-- Complete public contract for a finite bit-relation barrier table. -/
structure CertifiedTable {size : Nat} (profile : Profile size)
    (Length : Type*) (lengthValue : Length -> Nat)
    (relation : Length -> Fin size -> Fin size -> Bool)
    (Index : Type*) where
  semantic : SemanticCertificate profile Length lengthValue relation
  counts : CountCertificate profile Index

namespace CertifiedTable

variable {size : Nat} {profile : Profile size}
variable {Length : Type*} {lengthValue : Length -> Nat}
variable {relation : Length -> Fin size -> Fin size -> Bool}
variable {Index : Type*}

theorem storedSafe_eq
    (table : CertifiedTable profile Length lengthValue relation Index)
    (index : Index) :
    table.counts.storedSafe index =
      profile.safeCount (table.counts.leftLength index)
        (table.counts.rightLength index) :=
  table.counts.safeExact index

theorem storedFlat_eq
    (table : CertifiedTable profile Length lengthValue relation Index)
    (index : Index) :
    table.counts.storedFlat index =
      profile.flatCount (table.counts.leftLength index)
        (table.counts.rightLength index) :=
  table.counts.flatExact index

end CertifiedTable

end Hypostructure.Core.FiniteBitRelationBarrier
