import StructuralExhaustion.Core.AutomationFirst

namespace StructuralExhaustion.CT4

universe uDemand uPayer

/-- Demand/payer vocabulary for deterministic charging. -/
structure Spec (P : Core.Problem) where
  Demand : Type uDemand
  Payer : Type uPayer
  Eligible : Core.BranchContext P → Demand → Payer → Prop
  demandWeight : Core.BranchContext P → Demand → Nat
  capacity : Core.BranchContext P → Payer → Nat

end StructuralExhaustion.CT4
