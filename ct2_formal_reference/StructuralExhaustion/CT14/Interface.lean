namespace StructuralExhaustion.CT14.Interface

universe uA uB uR uL uC uM

/-! Import-cycle-free validated-entry contract for CT14 aggregate closure. -/

structure Framework where
  Ambient : Type uA
  BranchState : Ambient → Type uB
  ResidualClass : (G : Ambient) → BranchState G → Type uR
  LowerMass : (G : Ambient) → BranchState G → Type uL
  Capacity : (G : Ambient) → BranchState G → Type uC
  Multiplicity : (G : Ambient) → BranchState G → Type uM
  ScopeReady :
    {G : Ambient} → (branch : BranchState G) → ResidualClass G branch →
      LowerMass G branch → Capacity G branch → Multiplicity G branch → Prop
  C4Claim : (G : Ambient) → BranchState G → Prop

structure Input (F : Framework) where
  G : F.Ambient
  branch : F.BranchState G
  residual : F.ResidualClass G branch
  lowerMass : F.LowerMass G branch
  capacity : F.Capacity G branch
  multiplicity : F.Multiplicity G branch

def ScopeReadyAt (F : Framework) (input : Input F) : Prop :=
  F.ScopeReady input.branch input.residual input.lowerMass input.capacity
    input.multiplicity

end StructuralExhaustion.CT14.Interface
