import Mathlib.Data.Fintype.Prod
import StructuralExhaustion.Core.Enumeration

namespace StructuralExhaustion.Core.FiniteJointCapacity

universe u

/-!
# Joint capacity of two supplied finite schedules

This profile records an injective encoding of pairs drawn from two explicit,
duplicate-free schedules into one exact finite code type.  The capacity proof
uses finite-type cardinality only.  It does not construct the Cartesian list,
scan pairs, or inspect an ambient universe.
-/

/-- Two supplied local schedules and their joint encoding into one exact code
universe.  Injectivity is required only on entries of the supplied schedules;
the ambient left and right types need not be finite. -/
structure Profile where
  Left : Type u
  Right : Type u
  Code : Type u
  left : Core.OrderedCollection Left
  right : Core.OrderedCollection Right
  codes : FinEnum Code
  encode : Left → Right → Code
  encodeInjectiveOnSchedules :
    ∀ {left₁ left₂ right₁ right₂},
      left₁ ∈ left.values → left₂ ∈ left.values →
      right₁ ∈ right.values → right₂ ∈ right.values →
      encode left₁ right₁ = encode left₂ right₂ →
      left₁ = left₂ ∧ right₁ = right₂

namespace Profile

/-- Number of semantic checks performed by the joint-capacity theorem.  The
encoder and its injectivity proof are supplied certificates, so cardinality
transport performs no pair scan. -/
def checks (_profile : Profile) : Nat := 0

@[simp]
theorem checks_eq_zero (profile : Profile) : profile.checks = 0 := rfl

/-- The exact cardinality bound for the two supplied schedules.  The proof
reasons about the product of their finite membership subtypes, but no product
collection is ever defined or evaluated. -/
theorem left_mul_right_le_codeCard (profile : Profile) :
    profile.left.values.length * profile.right.values.length ≤
      profile.codes.card := by
  letI : DecidableEq profile.Left := profile.left.decEq
  letI : DecidableEq profile.Right := profile.right.decEq
  letI : FinEnum profile.Code := profile.codes
  letI : Fintype profile.Code := @FinEnum.instFintype _ profile.codes
  let LeftMember := ↥profile.left.toFinset
  let RightMember := ↥profile.right.toFinset
  letI : Fintype LeftMember := profile.left.toFinset.fintypeCoeSort
  letI : Fintype RightMember := profile.right.toFinset.fintypeCoeSort
  let jointEncode : LeftMember × RightMember → profile.Code :=
    fun pair => profile.encode pair.1.1 pair.2.1
  have jointInjective : Function.Injective jointEncode := by
    rintro ⟨left₁, right₁⟩ ⟨left₂, right₂⟩ equal
    have left₁Mem : left₁.1 ∈ profile.left.values :=
      (profile.left.mem_toFinset left₁.1).1 left₁.2
    have left₂Mem : left₂.1 ∈ profile.left.values :=
      (profile.left.mem_toFinset left₂.1).1 left₂.2
    have right₁Mem : right₁.1 ∈ profile.right.values :=
      (profile.right.mem_toFinset right₁.1).1 right₁.2
    have right₂Mem : right₂.1 ∈ profile.right.values :=
      (profile.right.mem_toFinset right₂.1).1 right₂.2
    obtain ⟨leftEqual, rightEqual⟩ :=
      profile.encodeInjectiveOnSchedules left₁Mem left₂Mem
        right₁Mem right₂Mem equal
    apply Prod.ext
    · exact Subtype.ext leftEqual
    · exact Subtype.ext rightEqual
  have cardBound := Fintype.card_le_of_injective jointEncode jointInjective
  have leftCard : Fintype.card LeftMember = profile.left.values.length := by
    calc
      Fintype.card LeftMember = profile.left.toFinset.card :=
        Fintype.card_coe profile.left.toFinset
      _ = profile.left.values.length :=
        List.toFinset_card_of_nodup profile.left.nodup
  have rightCard : Fintype.card RightMember = profile.right.values.length := by
    calc
      Fintype.card RightMember = profile.right.toFinset.card :=
        Fintype.card_coe profile.right.toFinset
      _ = profile.right.values.length :=
        List.toFinset_card_of_nodup profile.right.nodup
  rw [Fintype.card_prod LeftMember RightMember, leftCard, rightCard] at cardBound
  simpa [FinEnum.card_eq_fintypeCard] using cardBound

end Profile

end StructuralExhaustion.Core.FiniteJointCapacity
