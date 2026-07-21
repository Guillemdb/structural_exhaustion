import Hypostructure.CT17.Automation
import Hypostructure.Graph.Object

/-!
# Graph adapter for CT17

This adapter evaluates target-thickening semantics against the finite graph
object queried from the predecessor.  All schedules, searches, routing,
residuals, traces, and work accounting remain in the shared CT17 machine.
-/

namespace Hypostructure.Graph.CT17

universe uPrevious uVertex uTarget uOffset uPosition uValue

/-- Translate graph-indexed target, block, orbit, and compatibility semantics
into the domain-neutral CT17 contract. -/
def boundedTargetSpec {Previous : Type uPrevious}
    (object : Core.Residual.Query Previous fun _previous =>
      FiniteObject.{uVertex})
    (Target : Previous -> Type uTarget)
    (Offset : Previous -> Type uOffset)
    (Position : (previous : Previous) -> Nat -> Type uPosition)
    (Value : Previous -> Type uValue)
    (targetValue : (previous : Previous) -> FiniteObject.{uVertex} ->
      Target previous -> Value previous)
    (blockValue : (previous : Previous) -> FiniteObject.{uVertex} ->
      (scale : Nat) -> Position previous scale -> Offset previous ->
        Value previous)
    (orbitValue : (previous : Previous) -> FiniteObject.{uVertex} ->
      (scale : Nat) -> Offset previous -> Value previous)
    (Compatible : (previous : Previous) -> FiniteObject.{uVertex} ->
      Target previous -> Offset previous -> Prop) :
    _root_.Hypostructure.CT17.Spec Previous where
  Target := Target
  Offset := Offset
  Position := Position
  Value := Value
  targetValue := fun previous target =>
    targetValue previous (object.read previous) target
  blockValue := fun previous scale position offset =>
    blockValue previous (object.read previous) scale position offset
  orbitValue := fun previous scale offset =>
    orbitValue previous (object.read previous) scale offset
  Compatible := fun previous target offset =>
    Compatible previous (object.read previous) target offset

/-- Assemble the common CT17 capability from predecessor-owned graph
schedules and primitive graph-semantic decisions. -/
def boundedTargetCapability {Previous : Type uPrevious}
    (object : Core.Residual.Query Previous fun _previous =>
      FiniteObject.{uVertex})
    (Target : Previous -> Type uTarget)
    (Offset : Previous -> Type uOffset)
    (Position : (previous : Previous) -> Nat -> Type uPosition)
    (Value : Previous -> Type uValue)
    (targetValue : (previous : Previous) -> FiniteObject.{uVertex} ->
      Target previous -> Value previous)
    (blockValue : (previous : Previous) -> FiniteObject.{uVertex} ->
      (scale : Nat) -> Position previous scale -> Offset previous ->
        Value previous)
    (orbitValue : (previous : Previous) -> FiniteObject.{uVertex} ->
      (scale : Nat) -> Offset previous -> Value previous)
    (Compatible : (previous : Previous) -> FiniteObject.{uVertex} ->
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
      (selected : FiniteObject.{uVertex}) ->
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
      (boundedTargetSpec object Target Offset Position Value targetValue
        blockValue orbitValue Compatible) where
  targets := targets
  offsets := offsets
  scales := scales
  selectedScale := selectedScale
  selectedScale_mem := selectedScale_mem
  positions := positions
  finiteScaleLimit := finiteScaleLimit
  compatibleDecidable := fun previous target offset =>
    compatibleDecidable previous (object.read previous) target offset
  valueDecidableEq := valueDecidableEq
  inputSize := inputSize
  workCoefficient := workCoefficient
  workDegree := workDegree
  workBound := workBound

end Hypostructure.Graph.CT17
