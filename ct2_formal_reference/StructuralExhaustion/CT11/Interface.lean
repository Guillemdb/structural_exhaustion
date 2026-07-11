namespace StructuralExhaustion.CT11.Interface

universe uA uB uD uC uK uL

/-! Import-cycle-free validated-entry contract for CT11 localization. -/

structure Framework where
  Ambient : Type uA
  BranchState : Ambient → Type uB
  Deficit : (G : Ambient) → BranchState G → Type uD
  Decomposition : (G : Ambient) → BranchState G → Type uC
  Admissibility : (G : Ambient) → BranchState G → Type uK
  LocalType : (G : Ambient) → BranchState G → Type uL
  ScopeReady :
    {G : Ambient} → (branch : BranchState G) → Deficit G branch →
      Decomposition G branch → Admissibility G branch → LocalType G branch → Prop

structure Input (F : Framework) where
  G : F.Ambient
  branch : F.BranchState G
  deficit : F.Deficit G branch
  decomposition : F.Decomposition G branch
  admissibility : F.Admissibility G branch
  localType : F.LocalType G branch

def ScopeReadyAt (F : Framework) (input : Input F) : Prop :=
  F.ScopeReady input.branch input.deficit input.decomposition
    input.admissibility input.localType

end StructuralExhaustion.CT11.Interface
