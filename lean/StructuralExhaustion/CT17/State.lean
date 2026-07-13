import StructuralExhaustion.CT17.Capability

namespace StructuralExhaustion.CT17

universe uAmbient uBranch uTarget uOffset uPosition uValue

variable {P : Core.Problem.{uAmbient, uBranch}}
variable (S : Spec.{uAmbient, uBranch, uTarget, uOffset, uPosition, uValue} P)
variable (capability : Capability S)
variable (ctx : Core.BranchContext P)
variable (input : Input S capability ctx)

/-- A finite-scale position survives exactly when its entire offset block
avoids every target value. -/
def Survives (position : S.Position input.scale) : Prop :=
  ∀ target : S.Target, ∀ offset : S.Offset,
    S.blockValue ctx position offset ≠ S.targetValue target

/-- The large-scale orbit avoids the target at every declared offset. -/
def OrbitAvoids : Prop :=
  ∀ target : S.Target, ∀ offset : S.Offset,
    S.orbitValue ctx input.scale offset ≠ S.targetValue target

/-- First incompatible target/offset pair in deterministic enumeration order. -/
structure IncompatibilityResidual
    (C : Capability S) (context : Core.BranchContext P)
    (_invocation : Input S C context) where
  target : S.Target
  offset : S.Offset
  incompatible : ¬ S.Compatible context target offset

/-- State produced only after exhaustive compatibility search has found no
counterexample. -/
structure CompatibleState
    (C : Capability S) (context : Core.BranchContext P)
    (_invocation : Input S C context) : Prop where
  compatible : ∀ target : S.Target, ∀ offset : S.Offset,
    S.Compatible context target offset

/-- Exact finite-scale predecessor state. -/
structure FiniteScaleState
    (C : Capability S) (context : Core.BranchContext P)
    (invocation : Input S C context)
    (_compatible : CompatibleState S C context invocation) : Prop where
  finite : invocation.scale ≤ C.finiteScaleLimit

/-- Exact large-scale predecessor state. -/
structure OrbitScaleState
    (C : Capability S) (context : Core.BranchContext P)
    (invocation : Input S C context)
    (_compatible : CompatibleState S C context invocation) : Prop where
  large : C.finiteScaleLimit < invocation.scale

end StructuralExhaustion.CT17
