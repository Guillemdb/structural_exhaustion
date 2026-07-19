import StructuralExhaustion.CT5.Spec

namespace StructuralExhaustion.CT5

/-- Primitive executable data for CT5.  No field chooses a node outcome. -/
structure Capability {P : Core.Problem} (S : Spec P) where
  sites : FinEnum S.Site
  witnesses : (site : S.Site) → FinEnum (S.Witness site)
  activeDecidable : (ctx : Core.BranchContext P) →
    (site : S.Site) → Decidable (S.Active ctx site)
  supportsDecidable : (ctx : Core.BranchContext P) →
    (site : S.Site) → (witness : S.Witness site) →
      Decidable (S.Supports ctx site witness)
  required : Core.BranchContext P → Nat
  capacity : Core.BranchContext P → Nat

/-- CT5 consumes only the shared branch context. -/
abbrev Input (P : Core.Problem) := Core.BranchContext P

end StructuralExhaustion.CT5
