import StructuralExhaustion.Core.AutomationFirst

namespace StructuralExhaustion.CT5

universe uSite uWitness

/-- Problem-specific vocabulary for local-to-global bookkeeping. -/
structure Spec (P : Core.Problem) where
  Site : Type uSite
  Witness : Site → Type uWitness
  Active : Core.BranchContext P → Site → Prop
  Supports : (ctx : Core.BranchContext P) →
    (site : Site) → Witness site → Prop
  contribution : (ctx : Core.BranchContext P) →
    (site : Site) → Witness site → Nat

end StructuralExhaustion.CT5
