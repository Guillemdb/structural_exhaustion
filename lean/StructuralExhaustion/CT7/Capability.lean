import StructuralExhaustion.CT7.Spec

namespace StructuralExhaustion.CT7

structure Capability {P : Core.Problem} (S : Spec P) where
  contexts : (ctx : Core.BranchContext P) →
    (left right : S.Object) → FinEnum S.Context
  realizesDecidable : (ctx : Core.BranchContext P) →
    (object : S.Object) → (context : S.Context) →
      Decidable (S.Realizes ctx object context)

/-- A same-context pair of representatives. -/
structure Input {P : Core.Problem} (S : Spec P)
    (context : Core.BranchContext P) where
  left : S.Object
  right : S.Object

namespace Capability

/-- Route-facing CT7 trigger.  A route inherits the shared context and adds
only the two representatives. -/
def tacticInterface {P : Core.Problem} {S : Spec P}
    (_capability : Capability S) : Core.Routing.TacticInterface where
  Context := Core.BranchContext P
  Trigger := Input S

end Capability

end StructuralExhaustion.CT7
