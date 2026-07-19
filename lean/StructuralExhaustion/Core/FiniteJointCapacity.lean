import Mathlib.Data.Fintype.Prod
import Mathlib.SetTheory.Cardinal.Finite
import StructuralExhaustion.Core.Enumeration

namespace StructuralExhaustion.Core.FiniteJointCapacity

universe uLeft uRight uCode uGlobal uPrevious

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
  Left : Type uLeft
  Right : Type uRight
  Code : Type uCode
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

/-- Framework-owned semantic producer for a recoverable join of two supplied
finite state families.  Applications provide the concrete gluing operation
and the two recovery laws; injectivity of the pair encoding is then derived
once here.  In particular, an application must not restate pair injectivity
as a problem-specific field.

`Previous` is the complete accumulated residual consumed by the producer.
Indexing the join by that value prevents a later node from silently rebuilding
either state family independently of its incoming ledger. -/
structure RecoverableJoin (Previous : Sort uPrevious) (previous : Previous) where
  Left : Type uLeft
  Right : Type uRight
  Global : Type uGlobal
  Code : Type uCode
  left : Core.OrderedCollection Left
  right : Core.OrderedCollection Right
  codes : FinEnum Code
  glue : Left → Right → Global
  recoverLeft : Global → Left
  recoverRight : Global → Right
  recoverLeft_glue : ∀ leftState rightState,
    recoverLeft (glue leftState rightState) = leftState
  recoverRight_glue : ∀ leftState rightState,
    recoverRight (glue leftState rightState) = rightState
  code : Global → Code
  codeInjectiveOnGlue : ∀ {left₁ left₂ right₁ right₂},
    code (glue left₁ right₁) = code (glue left₂ right₂) →
      glue left₁ right₁ = glue left₂ right₂

namespace RecoverableJoin

/-- Forget semantic recovery only after deriving the schedule-level
injectivity required by the zero-enumeration capacity theorem. -/
noncomputable def profile {Previous : Sort uPrevious} {previous : Previous}
    (join : RecoverableJoin Previous previous) : Profile where
  Left := join.Left
  Right := join.Right
  Code := join.Code
  left := join.left
  right := join.right
  codes := join.codes
  encode := fun leftState rightState => join.code (join.glue leftState rightState)
  encodeInjectiveOnSchedules := by
    intro left₁ left₂ right₁ right₂ _ _ _ _ equal
    have glued : join.glue left₁ right₁ = join.glue left₂ right₂ :=
      join.codeInjectiveOnGlue equal
    exact ⟨by
      simpa only [join.recoverLeft_glue] using congrArg join.recoverLeft glued,
      by simpa only [join.recoverRight_glue] using congrArg join.recoverRight glued⟩

end RecoverableJoin

/-- Symbolic finite-type variant of `RecoverableJoin`.  It is used when an
application's mathematical family is a predicate-defined finite subtype whose
cardinality must remain symbolic: no ordered list of all inhabitants is
constructed or inspected. -/
structure RecoverableTypeJoin (Previous : Sort uPrevious) (previous : Previous) where
  Left : Type uLeft
  Right : Type uRight
  Global : Type uGlobal
  Code : Type uCode
  leftFinite : Finite Left
  rightFinite : Finite Right
  codeFinite : Finite Code
  glue : Left → Right → Global
  recoverLeft : Global → Left
  recoverRight : Global → Right
  recoverLeft_glue : ∀ leftState rightState,
    recoverLeft (glue leftState rightState) = leftState
  recoverRight_glue : ∀ leftState rightState,
    recoverRight (glue leftState rightState) = rightState
  code : Global → Code
  codeInjectiveOnGlue : ∀ {left₁ left₂ right₁ right₂},
    code (glue left₁ right₁) = code (glue left₂ right₂) →
      glue left₁ right₁ = glue left₂ right₂

namespace RecoverableTypeJoin

/-- Recoverability makes the symbolic pair-to-code map injective. -/
theorem encodeInjective {Previous : Sort uPrevious} {previous : Previous}
    (join : RecoverableTypeJoin Previous previous) :
    Function.Injective (fun pair : join.Left × join.Right ↦
      join.code (join.glue pair.1 pair.2)) := by
  rintro ⟨left₁, right₁⟩ ⟨left₂, right₂⟩ equal
  have glued : join.glue left₁ right₁ = join.glue left₂ right₂ :=
    join.codeInjectiveOnGlue equal
  apply Prod.ext
  · simpa only [join.recoverLeft_glue] using congrArg join.recoverLeft glued
  · simpa only [join.recoverRight_glue] using congrArg join.recoverRight glued

/-- Exact symbolic product capacity.  The proof uses only finite-type
cardinality transport and never exposes a list of pairs or code values. -/
theorem card_mul_card_le_codeCard
    {Previous : Sort uPrevious} {previous : Previous}
    (join : RecoverableTypeJoin Previous previous) :
    Nat.card join.Left * Nat.card join.Right ≤ Nat.card join.Code := by
  letI : Finite join.Left := join.leftFinite
  letI : Finite join.Right := join.rightFinite
  letI : Finite join.Code := join.codeFinite
  rw [← Nat.card_prod]
  exact Nat.card_le_card_of_injective
      (fun pair : join.Left × join.Right ↦
        join.code (join.glue pair.1 pair.2))
      join.encodeInjective

/-- The symbolic join performs no semantic scan. -/
def checks {Previous : Sort uPrevious} {previous : Previous}
    (_join : RecoverableTypeJoin Previous previous) : Nat := 0

@[simp] theorem checks_eq_zero
    {Previous : Sort uPrevious} {previous : Previous}
    (join : RecoverableTypeJoin Previous previous) : join.checks = 0 := rfl

end RecoverableTypeJoin

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

namespace RecoverableJoin

/-- A recoverable join pays its exact product cardinality without constructing
or traversing the product schedule. -/
theorem left_mul_right_le_codeCard
    {Previous : Sort uPrevious} {previous : Previous}
    (join : RecoverableJoin Previous previous) :
    join.left.values.length * join.right.values.length ≤ join.codes.card :=
  join.profile.left_mul_right_le_codeCard

end RecoverableJoin

end StructuralExhaustion.Core.FiniteJointCapacity
