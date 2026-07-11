namespace StructuralExhaustion.CT13.Interface

universe uA uB uT uH uR

/-! Import-cycle-free validated-entry contract for CT13 tiered charging. -/

structure Framework where
  Ambient : Type uA
  BranchState : Ambient → Type uB
  TierAccount : (G : Ambient) → BranchState G → Type uT
  Availability : (G : Ambient) → BranchState G → Type uH
  Resource : (G : Ambient) → BranchState G → Type uR
  ScopeReady :
    {G : Ambient} → (branch : BranchState G) → TierAccount G branch →
      Availability G branch → Resource G branch → Prop
  C4Claim : (G : Ambient) → BranchState G → Prop

structure Input (F : Framework) where
  G : F.Ambient
  branch : F.BranchState G
  account : F.TierAccount G branch
  availability : F.Availability G branch
  resource : F.Resource G branch

def ScopeReadyAt (F : Framework) (input : Input F) : Prop :=
  F.ScopeReady input.branch input.account input.availability input.resource

end StructuralExhaustion.CT13.Interface
