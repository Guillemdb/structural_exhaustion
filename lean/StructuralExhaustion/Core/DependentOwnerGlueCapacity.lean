import StructuralExhaustion.Core.Enumeration
import Mathlib

namespace StructuralExhaustion.Core.DependentOwnerGlueCapacity

open scoped BigOperators

universe u v w z

/-- A many-owner semantic glue whose choices are recoverable and whose glued
objects have an injective finite code. -/
structure Profile where
  Owner : Type u
  owners : FinEnum Owner
  Local : Owner → Type v
  locals : ∀ owner, FinEnum (Local owner)
  Global : Type w
  Code : Type z
  codes : FinEnum Code
  glue : (∀ owner, Local owner) → Global
  restrict : Global → ∀ owner, Local owner
  recover : ∀ choice owner, restrict (glue choice) owner = choice owner
  code : Global → Code
  codeInjectiveOnGlue : ∀ left right,
    code (glue left) = code (glue right) → glue left = glue right

namespace Profile

/-- Sum a natural owner weight over the profile's exact finite owner type. -/
noncomputable def weightSum (profile : Profile) (weight : profile.Owner → Nat) : Nat := by
  letI : Fintype profile.Owner := @FinEnum.instFintype _ profile.owners
  letI : DecidableEq profile.Owner := Classical.decEq _
  exact ∑ owner, weight owner

theorem weightSum_add (profile : Profile) (left right : profile.Owner → Nat) :
    profile.weightSum (fun owner => left owner + right owner) =
      profile.weightSum left + profile.weightSum right := by
  simp [weightSum, Finset.sum_add_distrib]

theorem weightSum_const (profile : Profile) (constant : Nat) :
    profile.weightSum (fun _ => constant) = profile.owners.card * constant := by
  unfold weightSum
  letI : Fintype profile.Owner := @FinEnum.instFintype _ profile.owners
  rw [Finset.sum_const, Finset.card_univ,
    ← @FinEnum.card_eq_fintypeCard _ profile.owners]
  simp

theorem weightSum_mono (profile : Profile) {left right : profile.Owner → Nat}
    (pointwise : ∀ owner, left owner ≤ right owner) :
    profile.weightSum left ≤ profile.weightSum right := by
  unfold weightSum
  exact Finset.sum_le_sum fun owner _ => pointwise owner

theorem glue_injective (profile : Profile) : Function.Injective profile.glue := by
  intro left right equal
  funext owner
  calc
    left owner = profile.restrict (profile.glue left) owner :=
      (profile.recover left owner).symm
    _ = profile.restrict (profile.glue right) owner := congrArg (fun g => profile.restrict g owner) equal
    _ = right owner := profile.recover right owner

theorem code_glue_injective (profile : Profile) :
    Function.Injective (fun choice => profile.code (profile.glue choice)) := by
  intro left right equal
  exact profile.glue_injective (profile.codeInjectiveOnGlue left right equal)

/-- Exact dependent product capacity, proved by cardinality transport only. -/
theorem localProduct_le_codeCard (profile : Profile) :
    Nat.card (∀ owner, profile.Local owner) ≤ profile.codes.card := by
  letI : Fintype profile.Owner := @FinEnum.instFintype _ profile.owners
  letI (owner : profile.Owner) : Fintype (profile.Local owner) :=
    @FinEnum.instFintype _ (profile.locals owner)
  letI : Fintype (∀ owner, profile.Local owner) := Fintype.ofFinite _
  letI : Fintype profile.Code := @FinEnum.instFintype _ profile.codes
  have bound := Fintype.card_le_of_injective
    (fun choice => profile.code (profile.glue choice)) profile.code_glue_injective
  simpa [Nat.card_eq_fintype_card, FinEnum.card_eq_fintypeCard] using bound

/-- Aggregate ownerwise powered lower bounds through the recoverable dependent
glue.  The proof uses only finite cardinalities and a product over the supplied
owner enumeration; it never materializes the Cartesian choice family. -/
theorem base_pow_sumWeight_le_codeCard_pow
    (profile : Profile) (base exponent : Nat) (weight : profile.Owner → Nat)
    (localLower : ∀ owner,
      base ^ weight owner ≤ Nat.card (profile.Local owner) ^ exponent) :
    base ^ profile.weightSum weight ≤ profile.codes.card ^ exponent := by
  letI : Fintype profile.Owner := @FinEnum.instFintype _ profile.owners
  letI : DecidableEq profile.Owner := Classical.decEq _
  letI (owner : profile.Owner) : Fintype (profile.Local owner) :=
    @FinEnum.instFintype _ (profile.locals owner)
  letI : Fintype profile.Code := @FinEnum.instFintype _ profile.codes
  change base ^ (∑ owner, weight owner) ≤ profile.codes.card ^ exponent
  have productLower :
      base ^ (∑ owner, weight owner) ≤
        (∏ owner, Nat.card (profile.Local owner)) ^ exponent := by
    calc
      base ^ (∑ owner, weight owner) =
          ∏ owner, base ^ weight owner := by
        symm
        exact Finset.prod_pow_eq_pow_sum Finset.univ weight base
      _ ≤ ∏ owner, Nat.card (profile.Local owner) ^ exponent := by
        exact Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
          (fun owner _ => localLower owner)
      _ = (∏ owner, Nat.card (profile.Local owner)) ^ exponent := by
        exact Finset.prod_pow Finset.univ exponent
          (fun owner => Nat.card (profile.Local owner))
  have productCard :
      (∏ owner, Nat.card (profile.Local owner)) =
        Nat.card (∀ owner, profile.Local owner) := by
    simp only [Nat.card_eq_fintype_card]
    exact (@Fintype.card_pi profile.Owner profile.Local _ _ _).symm
  rw [productCard] at productLower
  exact productLower.trans (Nat.pow_le_pow_left profile.localProduct_le_codeCard exponent)

end Profile

end StructuralExhaustion.Core.DependentOwnerGlueCapacity
