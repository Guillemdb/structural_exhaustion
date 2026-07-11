namespace StructuralExhaustion.CT7.Interface

universe uA uB uO uI uE uC

/-! Import-cycle-free validated-entry contract for CT7. -/

structure Framework where
  Ambient : Type uA
  BranchState : Ambient → Type uB
  Object : (G : Ambient) → BranchState G → Type uO
  Boundary : (G : Ambient) → BranchState G → Type uI
  ExchangeWitness : (G : Ambient) → BranchState G → Type uE
  ContextSystem : (G : Ambient) → BranchState G → Type uC
  ScopeReady :
    {G : Ambient} → (branch : BranchState G) →
    Object G branch → Object G branch → Boundary G branch →
    ExchangeWitness G branch → ContextSystem G branch → Prop
  C1Claim : (G : Ambient) → BranchState G → Prop
  C2Claim : (G : Ambient) → BranchState G → Prop
  C3Claim : (G : Ambient) → BranchState G → Prop

structure Input (F : Framework) where
  G : F.Ambient
  branch : F.BranchState G
  left : F.Object G branch
  right : F.Object G branch
  boundary : F.Boundary G branch
  exchange : F.ExchangeWitness G branch
  contexts : F.ContextSystem G branch

def ScopeReadyAt (F : Framework) (input : Input F) : Prop :=
  F.ScopeReady input.branch input.left input.right input.boundary
    input.exchange input.contexts

end StructuralExhaustion.CT7.Interface
