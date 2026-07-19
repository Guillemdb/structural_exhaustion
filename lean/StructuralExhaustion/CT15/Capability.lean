import StructuralExhaustion.CT15.Spec

namespace StructuralExhaustion.CT15

universe uAmbient uBranch uCoordinate

/-- The complete executable capability.  It contains only the exact
coordinate enumerator and the decider for primitive dependence semantics. -/
structure Capability {P : Core.Problem.{uAmbient, uBranch}}
    (S : Spec P) where
  coordinates : FinEnum S.Coordinate
  targetDependentDecidable : (ctx : Core.BranchContext P) →
    (coordinate : S.Coordinate) → Decidable (S.TargetDependent ctx coordinate)

/-- CT15 consumes the shared branch context directly. -/
abbrev Input (P : Core.Problem.{uAmbient, uBranch}) := Core.BranchContext P

end StructuralExhaustion.CT15
