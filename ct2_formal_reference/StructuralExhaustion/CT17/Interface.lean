namespace StructuralExhaustion.CT17.Interface

universe uA uB uS uO uC uR

/-! Import-cycle-free validated-entry contract for CT17 target thickening. -/

structure Framework where
  Ambient : Type uA
  BranchState : Ambient → Type uB
  TargetSet : (G : Ambient) → BranchState G → Type uS
  OffsetFamily : (G : Ambient) → BranchState G → Type uO
  CompletionClasses : (G : Ambient) → BranchState G → Type uC
  ArithmeticData : (G : Ambient) → BranchState G → Type uR
  ScopeReady :
    {G : Ambient} → (branch : BranchState G) → TargetSet G branch →
      OffsetFamily G branch → CompletionClasses G branch →
      ArithmeticData G branch → Prop
  C1Claim : (G : Ambient) → BranchState G → Prop
  C5Claim : (G : Ambient) → BranchState G → Prop

structure Input (F : Framework) where
  G : F.Ambient
  branch : F.BranchState G
  targetSet : F.TargetSet G branch
  offsets : F.OffsetFamily G branch
  completions : F.CompletionClasses G branch
  arithmetic : F.ArithmeticData G branch

def ScopeReadyAt (F : Framework) (input : Input F) : Prop :=
  F.ScopeReady input.branch input.targetSet input.offsets input.completions
    input.arithmetic

end StructuralExhaustion.CT17.Interface
