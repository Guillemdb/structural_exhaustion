namespace StructuralExhaustion.CT16.Interface

universe uA uB uS uD uT

/-! Import-cycle-free validated-entry contract for CT16 whole-object types. -/

structure Framework where
  Ambient : Type uA
  BranchState : Ambient → Type uB
  Support : (G : Ambient) → BranchState G → Type uS
  WholeDatum : (G : Ambient) → BranchState G → Type uD
  ClosedTypeData : (G : Ambient) → BranchState G → Type uT
  ScopeReady :
    {G : Ambient} → (branch : BranchState G) → Support G branch →
      WholeDatum G branch → ClosedTypeData G branch → Prop
  C2Claim : (G : Ambient) → BranchState G → Prop

structure Input (F : Framework) where
  G : F.Ambient
  branch : F.BranchState G
  support : F.Support G branch
  datum : F.WholeDatum G branch
  closedType : F.ClosedTypeData G branch

def ScopeReadyAt (F : Framework) (input : Input F) : Prop :=
  F.ScopeReady input.branch input.support input.datum input.closedType

end StructuralExhaustion.CT16.Interface
