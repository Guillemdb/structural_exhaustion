import StructuralExhaustion.Core.DependentOwnerGlueCapacity
import StructuralExhaustion.Core.EnumerationCombinators

namespace StructuralExhaustion.Examples.DependentOwnerGlueCapacity

open StructuralExhaustion.Core

def profile : Core.DependentOwnerGlueCapacity.Profile where
  Owner := Fin 2
  owners := inferInstance
  Local := fun _ => Fin 2
  locals := fun _ => inferInstance
  Global := Fin 2 × Fin 2
  Code := Fin 2 × Fin 2
  codes := inferInstance
  glue := fun choice => (choice 0, choice 1)
  restrict := fun global owner => if owner = 0 then global.1 else global.2
  recover := by
    intro choice owner
    fin_cases owner <;> simp
  code := id
  codeInjectiveOnGlue := by
    intro left right equal
    exact equal

example : Function.Injective profile.glue := profile.glue_injective

example : Function.Injective (fun choice => profile.code (profile.glue choice)) :=
  profile.code_glue_injective

example : Nat.card (∀ owner, profile.Local owner) ≤ profile.codes.card :=
  profile.localProduct_le_codeCard

/-- Two owners each pay one binary unit, so the dependent glue carries their
sum into the four-element code family without enumerating choice tuples. -/
example : 2 ^ profile.weightSum (fun _ => 1) ≤ profile.codes.card := by
  apply profile.base_pow_sumWeight_le_codeCard_pow 2 1 (fun _ => 1)
  intro owner
  simp [profile]

/-- A separate symbolic base bit coexists with both owner bits.  The generic
profile derives the eight-state capacity without constructing a product
schedule. -/
noncomputable def baseProfile :
    Core.DependentOwnerGlueCapacity.BaseProfile where
  Base := Bool
  finiteBase := inferInstance
  Owner := Fin 2
  owners := inferInstance
  Local := fun _ => Bool
  locals := fun _ => Core.Enumeration.bool
  Global := Bool × (Bool × Bool)
  Code := Bool × (Bool × Bool)
  codes := Enumeration.prod Enumeration.bool
    (Enumeration.prod Enumeration.bool Enumeration.bool)
  glue := fun base choice => (base, choice 0, choice 1)
  recoverBase := Prod.fst
  recoverLocal := fun global owner =>
    if owner = 0 then global.2.1 else global.2.2
  recoverBase_glue := by simp
  recoverLocal_glue := by
    intro base choice owner
    fin_cases owner <;> simp
  code := id
  codeInjectiveOnGlue := by
    intro leftBase rightBase leftChoice rightChoice equal
    exact equal

example :
    Nat.card baseProfile.Base *
        Nat.card (∀ owner, baseProfile.Local owner) ≤
      baseProfile.codes.card :=
  baseProfile.base_mul_localProduct_le_codeCard

example :
    Nat.card baseProfile.Base *
        2 ^ baseProfile.weightSum (fun _ => 1) ≤
      baseProfile.codes.card := by
  simpa using baseProfile.base_pow_mul_base_pow_sumWeight_le_codeCard_pow
    2 1 (fun _ => 1) (by intro owner; simp [baseProfile])

end StructuralExhaustion.Examples.DependentOwnerGlueCapacity
