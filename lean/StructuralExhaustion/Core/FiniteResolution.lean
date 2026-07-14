import StructuralExhaustion.Core.Enumeration

namespace StructuralExhaustion.Core.FiniteResolution

universe uSite uWitness

/-!
# Proof-level total resolution of a finite site family

This profile packages the exact contrapositive used before a dependent CT12
ledger: either every declared site has a mathematical witness, or one literal
site has no witness.  The proof uses classical logic only and performs no
product enumeration or witness search.
-/

structure Profile (Site : Type uSite) where
  Witness : Site → Type uWitness
  sites : FinEnum Site

namespace Profile

variable {Site : Type uSite}
  (profile : Profile.{uSite, uWitness} Site)

structure FullResolution where
  witness : (site : Site) → profile.Witness site

def Unresolved : Prop :=
  ∃ site : Site, ¬Nonempty (profile.Witness site)

/-- Exact finite-site state-space split.  This is proof-level choice, not an
executable traversal of the dependent witness product. -/
theorem fullResolution_or_unresolved :
    Nonempty profile.FullResolution ∨ profile.Unresolved := by
  classical
  by_cases complete : ∀ site, Nonempty (profile.Witness site)
  · exact Or.inl ⟨⟨fun site => Classical.choice (complete site)⟩⟩
  · exact Or.inr (Classical.not_forall.mp complete)

end Profile

end StructuralExhaustion.Core.FiniteResolution
