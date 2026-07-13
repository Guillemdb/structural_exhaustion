import StructuralExhaustion.CT2.ContextSystem

namespace StructuralExhaustion.CT2

universe uAmbient uBranch

/-! Executable baseline and target observations. -/

structure Observable (P : Core.Problem.{uAmbient, uBranch})
    (Target : P.Ambient → Prop) where
  baselineDecidable : (G : P.Ambient) → Decidable (P.Baseline G)
  targetDecidable : (G : P.Ambient) → Decidable (Target G)

end StructuralExhaustion.CT2
