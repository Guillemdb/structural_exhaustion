import StructuralExhaustion.CT6.Spec

namespace StructuralExhaustion.CT6

structure Capability {P : Core.Problem} (S : Spec P) where
  failureOrder : FinEnum S.Index
  failureDecidable : (ctx : Core.BranchContext P) →
    (index : S.Index) → Decidable (S.Failure ctx index)

abbrev Input (P : Core.Problem) := Core.BranchContext P

namespace Capability

/-- Route-facing CT6 trigger; the shared context contains the complete input. -/
def tacticInterface {P : Core.Problem} {S : Spec P}
    (_capability : Capability S) : Core.Routing.TacticInterface where
  Context := Core.BranchContext P
  Trigger := fun _ => Unit

end Capability

end StructuralExhaustion.CT6
