import StructuralExhaustion.Core.AutomationFirst

namespace StructuralExhaustion.CT6

universe uIndex uData

/-- Problem-specific monitored family and first-failure semantics. -/
structure Spec (P : Core.Problem) where
  Index : Type uIndex
  FailureData : Type uData
  Failure : Core.BranchContext P → Index → Prop
  failureData : (ctx : Core.BranchContext P) →
    (index : Index) → Failure ctx index → FailureData
  contribution : Core.BranchContext P → Index → Nat

end StructuralExhaustion.CT6
