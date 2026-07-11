namespace StructuralExhaustion.CT10.Interface

universe uA uB uR uD uL uT

/-! Import-cycle-free validated-entry contract for CT10. -/

structure Framework where
  Ambient : Type uA
  BranchState : Ambient → Type uB
  ResidualClass : (G : Ambient) → BranchState G → Type uR
  MissingDatum : (G : Ambient) → BranchState G → Type uD
  Alphabet : (G : Ambient) → BranchState G → Type uL
  ClassTable : (G : Ambient) → BranchState G → Type uT
  ScopeReady :
    {G : Ambient} → (branch : BranchState G) →
    ResidualClass G branch → MissingDatum G branch →
    Alphabet G branch → ClassTable G branch → Prop
  C5Claim : (G : Ambient) → BranchState G → Prop

structure Input (F : Framework) where
  G : F.Ambient
  branch : F.BranchState G
  residual : F.ResidualClass G branch
  datum : F.MissingDatum G branch
  alphabet : F.Alphabet G branch
  table : F.ClassTable G branch

def ScopeReadyAt (F : Framework) (input : Input F) : Prop :=
  F.ScopeReady input.branch input.residual input.datum input.alphabet input.table

end StructuralExhaustion.CT10.Interface
