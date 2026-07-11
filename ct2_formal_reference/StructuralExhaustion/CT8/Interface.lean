namespace StructuralExhaustion.CT8.Interface

universe uA uB uS uT uH

/-! Import-cycle-free validated-entry contract for CT8. -/

structure Framework where
  Ambient : Type uA
  BranchState : Ambient → Type uB
  Sequence : (G : Ambient) → BranchState G → Type uS
  TypeSystem : (G : Ambient) → BranchState G → Type uT
  Threshold : (G : Ambient) → BranchState G → Type uH
  ScopeReady :
    {G : Ambient} → (branch : BranchState G) →
    Sequence G branch → TypeSystem G branch → Threshold G branch → Prop
  C2Claim : (G : Ambient) → BranchState G → Prop
  C5Claim : (G : Ambient) → BranchState G → Prop

structure Input (F : Framework) where
  G : F.Ambient
  branch : F.BranchState G
  sequence : F.Sequence G branch
  typeSystem : F.TypeSystem G branch
  threshold : F.Threshold G branch

def ScopeReadyAt (F : Framework) (input : Input F) : Prop :=
  F.ScopeReady input.branch input.sequence input.typeSystem input.threshold

end StructuralExhaustion.CT8.Interface
