import StructuralExhaustion.CT17.Spec

namespace StructuralExhaustion.CT17

universe uAmbient uBranch uTarget uOffset uPosition uValue

/-! The complete problem-specific CT17 API.  Every field is primitive
mathematical data, a finite enumerator, or a decision procedure. -/

structure Capability
    {P : Core.Problem.{uAmbient, uBranch}}
    (S : Spec.{uAmbient, uBranch, uTarget, uOffset, uPosition, uValue} P) where
  targets : FinEnum S.Target
  offsets : FinEnum S.Offset
  positions : (scale : Nat) → FinEnum (S.Position scale)
  compatibleDecidable : (ctx : Core.BranchContext P) →
    (target : S.Target) → (offset : S.Offset) →
      Decidable (S.Compatible ctx target offset)
  valueDecidableEq : DecidableEq S.Value
  finiteScaleLimit : Nat

/-- Transition-facing invocation.  The inherited branch context is an index,
so a transition supplies only the scale at which CT17 must run. -/
structure Input
    {P : Core.Problem.{uAmbient, uBranch}}
    (S : Spec.{uAmbient, uBranch, uTarget, uOffset, uPosition, uValue} P)
    (_capability : Capability S) (_ctx : Core.BranchContext P) where
  scale : Nat

end StructuralExhaustion.CT17
