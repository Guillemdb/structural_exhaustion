import StructuralExhaustion.Core.AutomationFirst

namespace StructuralExhaustion.CT7

universe uObject uContext

/-- Exact exchange vocabulary.  Responses are executable truth values. -/
structure Spec (P : Core.Problem) where
  Object : Type uObject
  Context : Type uContext
  Realizes : Core.BranchContext P → Object → Context → Prop
  response : Core.BranchContext P → Object → Context → Bool

end StructuralExhaustion.CT7
