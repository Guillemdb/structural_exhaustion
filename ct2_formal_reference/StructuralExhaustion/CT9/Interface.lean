namespace StructuralExhaustion.CT9.Interface

universe uA uB uP uF uL uC

/-! Import-cycle-free validated-entry contract for CT9. -/

structure Framework where
  Ambient : Type uA
  BranchState : Ambient → Type uB
  Payer : (G : Ambient) → BranchState G → Type uP
  Fibre : (G : Ambient) → BranchState G → Type uF
  Labels : (G : Ambient) → BranchState G → Type uL
  Capacity : (G : Ambient) → BranchState G → Type uC
  ScopeReady :
    {G : Ambient} → (branch : BranchState G) →
    Payer G branch → Fibre G branch → Labels G branch → Capacity G branch → Prop
  C1Claim : (G : Ambient) → BranchState G → Prop

structure Input (F : Framework) where
  G : F.Ambient
  branch : F.BranchState G
  payer : F.Payer G branch
  fibre : F.Fibre G branch
  labels : F.Labels G branch
  capacity : F.Capacity G branch

def ScopeReadyAt (F : Framework) (input : Input F) : Prop :=
  F.ScopeReady input.branch input.payer input.fibre input.labels input.capacity

end StructuralExhaustion.CT9.Interface
