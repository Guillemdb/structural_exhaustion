import StructuralExhaustion.Core.AutomationFirst

namespace StructuralExhaustion.CT17

universe uAmbient uBranch uTarget uOffset uPosition uValue

/-! Primitive mathematical vocabulary for target thickening.  Search, graph,
and terminal semantics are defined by the downstream machine layers. -/

structure Spec (P : Core.Problem.{uAmbient, uBranch}) where
  Target : Type uTarget
  Offset : Type uOffset
  Position : Nat → Type uPosition
  Value : Type uValue
  targetValue : Target → Value
  blockValue : Core.BranchContext P → {scale : Nat} →
    Position scale → Offset → Value
  orbitValue : Core.BranchContext P → Nat → Offset → Value
  Compatible : Core.BranchContext P → Target → Offset → Prop

end StructuralExhaustion.CT17
