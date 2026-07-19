import StructuralExhaustion.CT6.Spec

namespace StructuralExhaustion.CT6

structure Capability {P : Core.Problem} (S : Spec P) where
  failureOrder : FinEnum S.Index
  failureDecidable : (ctx : Core.BranchContext P) →
    (index : S.Index) → Decidable (S.Failure ctx index)

abbrev Input (P : Core.Problem) := Core.BranchContext P

end StructuralExhaustion.CT6
