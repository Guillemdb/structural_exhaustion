namespace StructuralExhaustion.CT15.Interface

universe uA uB uT uR uD uC

/-! Import-cycle-free validated-entry contract for CT15 rank forcing. -/

structure Framework where
  Ambient : Type uA
  BranchState : Ambient → Type uB
  TestFamily : (G : Ambient) → BranchState G → Type uT
  RankMap : (G : Ambient) → BranchState G → Type uR
  TargetData : (G : Ambient) → BranchState G → Type uD
  Capacity : (G : Ambient) → BranchState G → Type uC
  ScopeReady :
    {G : Ambient} → (branch : BranchState G) → TestFamily G branch →
      RankMap G branch → TargetData G branch → Capacity G branch → Prop
  C4Claim : (G : Ambient) → BranchState G → Prop

structure Input (F : Framework) where
  G : F.Ambient
  branch : F.BranchState G
  tests : F.TestFamily G branch
  rankMap : F.RankMap G branch
  target : F.TargetData G branch
  capacity : F.Capacity G branch

def ScopeReadyAt (F : Framework) (input : Input F) : Prop :=
  F.ScopeReady input.branch input.tests input.rankMap input.target input.capacity

end StructuralExhaustion.CT15.Interface
