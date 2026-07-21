import Hypostructure.CT17.Automation
import Hypostructure.PDE.Model

/-!
# PDE adapter for CT17

The PDE layer evaluates bounded scale, shell, modulation, and compactification
arithmetic against one represented state queried from the predecessor.  It
does not enumerate a continuum or own any CT17 route.
-/

namespace Hypostructure.PDE.CT17

universe uPrevious uModel uTarget uOffset uPosition uValue

/-- Translate represented PDE target-thickening semantics into shared CT17. -/
def boundedScaleSpec {Previous : Type uPrevious}
    (M : LocalModel.{uModel})
    (state : Core.Residual.Query Previous fun _previous => M.problem.Ambient)
    (Target : Previous -> Type uTarget)
    (Offset : Previous -> Type uOffset)
    (Position : (previous : Previous) -> Nat -> Type uPosition)
    (Value : Previous -> Type uValue)
    (targetValue : (previous : Previous) -> M.problem.Ambient ->
      Target previous -> Value previous)
    (blockValue : (previous : Previous) -> M.problem.Ambient ->
      (scale : Nat) -> Position previous scale -> Offset previous ->
        Value previous)
    (orbitValue : (previous : Previous) -> M.problem.Ambient ->
      (scale : Nat) -> Offset previous -> Value previous)
    (Compatible : (previous : Previous) -> M.problem.Ambient ->
      Target previous -> Offset previous -> Prop) :
    _root_.Hypostructure.CT17.Spec Previous where
  Target := Target
  Offset := Offset
  Position := Position
  Value := Value
  targetValue := fun previous target =>
    targetValue previous (state.read previous) target
  blockValue := fun previous scale position offset =>
    blockValue previous (state.read previous) scale position offset
  orbitValue := fun previous scale offset =>
    orbitValue previous (state.read previous) scale offset
  Compatible := fun previous target offset =>
    Compatible previous (state.read previous) target offset

/-- Assemble shared CT17 from residual-owned finite PDE schedules and
primitive represented-state decisions. -/
def boundedScaleCapability {Previous : Type uPrevious}
    (M : LocalModel.{uModel})
    (state : Core.Residual.Query Previous fun _previous => M.problem.Ambient)
    (Target : Previous -> Type uTarget)
    (Offset : Previous -> Type uOffset)
    (Position : (previous : Previous) -> Nat -> Type uPosition)
    (Value : Previous -> Type uValue)
    (targetValue : (previous : Previous) -> M.problem.Ambient ->
      Target previous -> Value previous)
    (blockValue : (previous : Previous) -> M.problem.Ambient ->
      (scale : Nat) -> Position previous scale -> Offset previous ->
        Value previous)
    (orbitValue : (previous : Previous) -> M.problem.Ambient ->
      (scale : Nat) -> Offset previous -> Value previous)
    (Compatible : (previous : Previous) -> M.problem.Ambient ->
      Target previous -> Offset previous -> Prop)
    (targets : Core.Residual.Query Previous fun previous =>
      Core.Finite.Enumeration (Target previous))
    (offsets : Core.Residual.Query Previous fun previous =>
      Core.Finite.Enumeration (Offset previous))
    (scales : Core.Residual.Query Previous fun _previous =>
      Core.Finite.Enumeration Nat)
    (selectedScale : Core.Residual.Query Previous fun _previous => Nat)
    (selectedScale_mem : forall previous,
      selectedScale.read previous ∈ (scales.read previous).values)
    (positions : (scale : Nat) -> Core.Residual.Query Previous fun previous =>
      Core.Finite.Enumeration (Position previous scale))
    (finiteScaleLimit : Core.Residual.Query Previous fun _previous => Nat)
    (compatibleDecidable : (previous : Previous) ->
      (selected : M.problem.Ambient) ->
      (target : Target previous) -> (offset : Offset previous) ->
        Decidable (Compatible previous selected target offset))
    (valueDecidableEq : (previous : Previous) ->
      DecidableEq (Value previous))
    (inputSize : Previous -> Nat) (workCoefficient workDegree : Nat)
    (workBound : forall previous,
      _root_.Hypostructure.CT17.localCheckBound
          (targets.read previous) (offsets.read previous)
          ((positions (selectedScale.read previous)).read previous) <=
        workCoefficient * (inputSize previous + 1) ^ workDegree) :
    _root_.Hypostructure.CT17.Capability
      (boundedScaleSpec M state Target Offset Position Value targetValue
        blockValue orbitValue Compatible) where
  targets := targets
  offsets := offsets
  scales := scales
  selectedScale := selectedScale
  selectedScale_mem := selectedScale_mem
  positions := positions
  finiteScaleLimit := finiteScaleLimit
  compatibleDecidable := fun previous target offset =>
    compatibleDecidable previous (state.read previous) target offset
  valueDecidableEq := valueDecidableEq
  inputSize := inputSize
  workCoefficient := workCoefficient
  workDegree := workDegree
  workBound := workBound

end Hypostructure.PDE.CT17
