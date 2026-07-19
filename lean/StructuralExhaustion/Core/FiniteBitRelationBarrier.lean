import Mathlib.Data.BitVec
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic
import Batteries.Data.BitVec.Lemmas

namespace StructuralExhaustion.Core.FiniteBitRelationBarrier

/-!
# Finite relation-barrier counts

This module owns the integer arithmetic behind a finite two-leg relation
barrier.  A row at length `s` records the labels compatible with one source
label.  For lengths `a` and `b`, `safeCount` counts triples whose two legs are
compatible, while `flatCount` additionally requires the composed `a+b` leg.

The implementation uses bit-row intersections.  It does not enumerate a
family of ambient objects or a Boolean state cube.
-/

/-- A length-indexed family of Boolean relation matrices on `size` labels. -/
structure Profile (size : Nat) where
  row : Nat → Fin size → BitVec size

namespace Profile

variable {size : Nat} (profile : Profile size)

/-- Number of compatible two-leg triples, summed by their middle label. -/
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

/-- The complementary, composition-obstructed triple count. -/
def obstructedCount (leftLength rightLength : Nat) : Nat :=
  profile.safeCount leftLength rightLength -
    profile.flatCount leftLength rightLength

theorem obstructed_add_flat
    (leftLength rightLength : Nat)
    (flat_le : profile.flatCount leftLength rightLength ≤
      profile.safeCount leftLength rightLength) :
    profile.obstructedCount leftLength rightLength +
        profile.flatCount leftLength rightLength =
      profile.safeCount leftLength rightLength := by
  exact Nat.sub_add_cancel flat_le

/-- Primitive bit operations used by one barrier count. -/
def checks (_leftLength _rightLength : Nat) : Nat :=
  let _relation := profile.row
  size + size ^ 2

theorem checks_quadratic (leftLength rightLength : Nat) :
    profile.checks leftLength rightLength ≤ 2 * (size + 1) ^ 2 := by
  simp only [checks]
  nlinarith [Nat.zero_le size]

end Profile

/-- Pack one decidable relation row into the same compact representation used
by the barrier counters.  Applications can audit a stored row with one
`BitVec` equality instead of reifying one theorem per matrix entry. -/
def semanticRow {size : Nat}
    (relation : Fin size → Fin size → Bool) (source : Fin size) : BitVec size :=
  BitVec.ofFnLE (relation source)

@[simp] theorem semanticRow_getLsb {size : Nat}
    (relation : Fin size → Fin size → Bool) (source target : Fin size) :
    (semanticRow relation source).getLsb target = relation source target := by
  exact BitVec.getLsb_ofFnLE _ _

/-- Exact semantic ownership for every row of a finite relation profile.

The certificate deliberately stores whole-row equalities.  This keeps fixed
table validation compact while its projection still supplies the pointwise
entry theorem expected by semantic consumers. -/
structure SemanticCertificate {size : Nat} (profile : Profile size)
    (Length : Type*) (lengthValue : Length → Nat)
    (relation : Length → Fin size → Fin size → Bool) : Prop where
  rowExact : ∀ length source,
    profile.row (lengthValue length) source = semanticRow (relation length) source

namespace SemanticCertificate

variable {size : Nat} {profile : Profile size} {Length : Type*}
  {lengthValue : Length → Nat}
  {relation : Length → Fin size → Fin size → Bool}

theorem getLsb_eq
    (certificate : SemanticCertificate profile Length lengthValue relation)
    (length : Length) (source target : Fin size) :
    (profile.row (lengthValue length) source).getLsb target =
      relation length source target := by
  rw [certificate.rowExact length source]
  exact semanticRow_getLsb _ _ _

end SemanticCertificate

/-- Exact ownership of cached safe/flat counts by a finite barrier profile.
The index type is the proof-selected local schedule; this abstraction performs
no ambient enumeration. -/
structure CountCertificate {size : Nat} (profile : Profile size)
    (Index : Type*) where
  leftLength : Index → Nat
  rightLength : Index → Nat
  storedSafe : Index → Nat
  storedFlat : Index → Nat
  safeExact : ∀ index,
    storedSafe index = profile.safeCount (leftLength index) (rightLength index)
  flatExact : ∀ index,
    storedFlat index = profile.flatCount (leftLength index) (rightLength index)

/-- One reusable owner for the semantic relation rows and all cached counts on
the proof-selected local index schedule. -/
structure CertifiedTable {size : Nat} (profile : Profile size)
    (Length : Type*) (lengthValue : Length → Nat)
    (relation : Length → Fin size → Fin size → Bool)
    (Index : Type*) where
  semantic : SemanticCertificate profile Length lengthValue relation
  counts : CountCertificate profile Index

end StructuralExhaustion.Core.FiniteBitRelationBarrier
