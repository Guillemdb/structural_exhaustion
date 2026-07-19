import StructuralExhaustion.CT4.Spec

namespace StructuralExhaustion.CT4

structure Capability {P : Core.Problem} (S : Spec P) where
  demands : FinEnum S.Demand
  payers : FinEnum S.Payer
  eligibleDecidable : (ctx : Core.BranchContext P) →
    (demand : S.Demand) → (payer : S.Payer) →
      Decidable (S.Eligible ctx demand payer)
  required : Core.BranchContext P → Nat

abbrev Input (P : Core.Problem) := Core.BranchContext P

end StructuralExhaustion.CT4
