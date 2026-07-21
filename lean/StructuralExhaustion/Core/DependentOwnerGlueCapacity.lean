import StructuralExhaustion.Core.Enumeration
import Mathlib

namespace StructuralExhaustion.Core.DependentOwnerGlueCapacity

open scoped BigOperators

universe u v w z b

/-! ## Framework-owned realized projections -/

/-- The values actually realized by a projection of an existing carrier.

This is the single generic image view used by applications.  A proof node may
instantiate the projection carried by its incoming residual, but it must not
define an application-owned replacement family. -/
def RealizedProjection (Global : Type w) (Base : Type b)
    (project : Global → Base) :=
  {base : Base // ∃ global : Global, project global = base}

noncomputable instance realizedProjectionFinite
    (Global : Type w) (Base : Type b) (project : Global → Base)
    [Finite Base] : Finite (RealizedProjection Global Base project) := by
  exact Finite.of_injective Subtype.val Subtype.val_injective

/-- Every incoming global state yields its canonical realized projection. -/
def realizedProjectionValue {Global : Type w} {Base : Type b}
    (project : Global → Base) (global : Global) :
    RealizedProjection Global Base project :=
  ⟨project global, ⟨global, rfl⟩⟩

/-- The canonical realized-projection witness exposes exactly the value of
the incoming ledger projection.  Applications should rewrite with this
framework lemma rather than unfold the proof-carrying image subtype. -/
@[simp] theorem realizedProjectionValue_val
    {Global : Type w} {Base : Type b}
    (project : Global → Base) (global : Global) :
    (realizedProjectionValue project global).1 = project global := rfl

/-- Exact ordered enumeration of the values realized by a projection.

The source enumeration is the only carrier supplied by an application.  The
framework maps it through the projection, removes duplicate projected values,
and retains the existential realization proof in the subtype.  Consequently a
proof node never has to manufacture a second, application-owned state family
merely to enumerate the image of its incoming residual. -/
@[implicit_reducible]
noncomputable def realizedProjectionEnumeration
    {Global : Type w} {Base : Type b}
    (globals : FinEnum Global) (project : Global → Base) :
    FinEnum (RealizedProjection Global Base project) := by
  classical
  let values :=
    (globals.orderedValues.map (realizedProjectionValue project)).dedup
  apply FinEnum.ofNodupList values
  · rintro ⟨base, ⟨global, rfl⟩⟩
    simp [values, realizedProjectionValue]
  · exact List.nodup_dedup _

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

/-! ## One symbolic base state plus dependent local choices

This is the common capacity contract for a state family that must coexist
with every choice in a dependent local product.  The base family is kept
symbolic through `Finite`; only the already supplied owner and local
enumerations are used.  In particular, the theorem never enumerates the
Cartesian product of base states and local choices.
-/

/-- Recoverable gluing of one symbolic base state with one dependent family
of local choices into a common finite code universe. -/
structure BaseProfile where
  Base : Type b
  finiteBase : Finite Base
  Owner : Type u
  owners : FinEnum Owner
  Local : Owner → Type v
  locals : ∀ owner, FinEnum (Local owner)
  Global : Type w
  Code : Type z
  codes : FinEnum Code
  glue : Base → (∀ owner, Local owner) → Global
  recoverBase : Global → Base
  recoverLocal : Global → ∀ owner, Local owner
  recoverBase_glue : ∀ base choice,
    recoverBase (glue base choice) = base
  recoverLocal_glue : ∀ base choice owner,
    recoverLocal (glue base choice) owner = choice owner
  code : Global → Code
  codeInjectiveOnGlue : ∀ leftBase rightBase leftChoice rightChoice,
    code (glue leftBase leftChoice) = code (glue rightBase rightChoice) →
      glue leftBase leftChoice = glue rightBase rightChoice

namespace BaseProfile

variable (profile : BaseProfile)

noncomputable instance : Finite profile.Base := profile.finiteBase

noncomputable def weightSum (weight : profile.Owner → Nat) : Nat := by
  letI : Fintype profile.Owner := @FinEnum.instFintype _ profile.owners
  letI : DecidableEq profile.Owner := profile.owners.decEq
  exact ∑ owner, weight owner

/-- The common code recovers both the symbolic base and every local choice. -/
theorem code_glue_injective :
    Function.Injective (fun pair : profile.Base × (∀ owner, profile.Local owner) ↦
      profile.code (profile.glue pair.1 pair.2)) := by
  rintro ⟨leftBase, leftChoice⟩ ⟨rightBase, rightChoice⟩ equal
  have glued := profile.codeInjectiveOnGlue
    leftBase rightBase leftChoice rightChoice equal
  apply Prod.ext
  · simpa only [profile.recoverBase_glue] using
      congrArg profile.recoverBase glued
  · funext owner
    simpa only [profile.recoverLocal_glue] using
      congrArg (fun global ↦ profile.recoverLocal global owner) glued

/-- Exact symbolic joint capacity.  No base list or product schedule is
constructed. -/
theorem base_mul_localProduct_le_codeCard :
    Nat.card profile.Base * Nat.card (∀ owner, profile.Local owner) ≤
      profile.codes.card := by
  letI : Fintype profile.Owner := @FinEnum.instFintype _ profile.owners
  letI (owner : profile.Owner) : Fintype (profile.Local owner) :=
    @FinEnum.instFintype _ (profile.locals owner)
  letI : Fintype profile.Code := @FinEnum.instFintype _ profile.codes
  rw [← Nat.card_prod]
  have bound := Nat.card_le_card_of_injective
    (fun pair : profile.Base × (∀ owner, profile.Local owner) ↦
      profile.code (profile.glue pair.1 pair.2))
    profile.code_glue_injective
  simpa [FinEnum.card_eq_fintypeCard] using bound

/-- Aggregate ownerwise powered lower bounds while retaining the independent
symbolic base factor. -/
theorem base_pow_mul_base_pow_sumWeight_le_codeCard_pow
    (base exponent : Nat) (weight : profile.Owner → Nat)
    (localLower : ∀ owner,
      base ^ weight owner ≤ Nat.card (profile.Local owner) ^ exponent) :
    Nat.card profile.Base ^ exponent *
        base ^ profile.weightSum weight ≤
      profile.codes.card ^ exponent := by
  letI : Fintype profile.Owner := @FinEnum.instFintype _ profile.owners
  letI : DecidableEq profile.Owner := profile.owners.decEq
  letI (owner : profile.Owner) : Fintype (profile.Local owner) :=
    @FinEnum.instFintype _ (profile.locals owner)
  have localProductLower :
      base ^ (∑ owner, weight owner) ≤
        Nat.card (∀ owner, profile.Local owner) ^ exponent := by
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
      _ = Nat.card (∀ owner, profile.Local owner) ^ exponent := by
        have productCard :
            (∏ owner, Nat.card (profile.Local owner)) =
              Nat.card (∀ owner, profile.Local owner) := by
          simp only [Nat.card_eq_fintype_card]
          exact (@Fintype.card_pi profile.Owner profile.Local _ _ _).symm
        rw [productCard]
  have multiplied := Nat.mul_le_mul_left
    (Nat.card profile.Base ^ exponent) localProductLower
  calc
    Nat.card profile.Base ^ exponent *
        base ^ profile.weightSum weight =
        Nat.card profile.Base ^ exponent *
          base ^ (∑ owner, weight owner) := by
      rfl
    _ ≤ Nat.card profile.Base ^ exponent *
        Nat.card (∀ owner, profile.Local owner) ^ exponent := multiplied
    _ = (Nat.card profile.Base *
        Nat.card (∀ owner, profile.Local owner)) ^ exponent := by
      rw [Nat.mul_pow]
    _ ≤ profile.codes.card ^ exponent :=
      Nat.pow_le_pow_left profile.base_mul_localProduct_le_codeCard exponent

/-- Capacity transport is certificate-only. -/
def checks (_profile : BaseProfile) : Nat := 0

@[simp] theorem checks_eq_zero : profile.checks = 0 := rfl

end BaseProfile

end StructuralExhaustion.Core.DependentOwnerGlueCapacity
