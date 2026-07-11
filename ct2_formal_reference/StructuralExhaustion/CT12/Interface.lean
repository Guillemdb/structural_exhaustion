namespace StructuralExhaustion.CT12.Interface

universe uA uB uL uP

/-! Import-cycle-free validated-entry contract for CT12 peeling. -/

structure Framework where
  Ambient : Type uA
  BranchState : Ambient → Type uB
  LoadAccount : (G : Ambient) → BranchState G → Type uL
  PeelMove : (G : Ambient) → BranchState G → Type uP
  ScopeReady :
    {G : Ambient} → (branch : BranchState G) →
      LoadAccount G branch → PeelMove G branch → Nat → Prop
  C4Claim : (G : Ambient) → BranchState G → Prop

structure Input (F : Framework) where
  G : F.Ambient
  branch : F.BranchState G
  account : F.LoadAccount G branch
  peelMove : F.PeelMove G branch
  load : Nat

def ScopeReadyAt (F : Framework) (input : Input F) : Prop :=
  F.ScopeReady input.branch input.account input.peelMove input.load

end StructuralExhaustion.CT12.Interface
