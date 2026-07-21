import Hypostructure.Core.Coordinate.Path
import Hypostructure.Core.SemanticEquivalence

/-!
# Composite coordinate transport

Domain layers prove laws for primitive generators. Core derives the law for
every path, including identity and composition.
-/

namespace Hypostructure.Core

universe uAmbient uBranch uCoordinate uObject uPrimitive uObstruction

variable {P : Problem.{uAmbient, uBranch}}
  {C : CoordinateSystem.{uAmbient, uBranch, uCoordinate, uObject, uPrimitive} P}

/-- Every primitive action preserves the problem baseline. -/
structure PrimitiveBaselineTransport
    (C : CoordinateSystem.{uAmbient, uBranch, uCoordinate, uObject, uPrimitive} P) where
  preserves : forall {source target} (step : C.Primitive source target)
    (object : C.Object source),
    P.Baseline (C.realize source object) ->
      P.Baseline (C.realize target (C.act step object))

/-- Every primitive action transports the dependent branch state. -/
structure PrimitiveBranchStateTransport
    (C : CoordinateSystem.{uAmbient, uBranch, uCoordinate, uObject, uPrimitive} P) where
  transport : forall {source target} (step : C.Primitive source target)
    (object : C.Object source),
    P.BranchState (C.realize source object) ->
      P.BranchState (C.realize target (C.act step object))

/-- Every primitive action transports one theorem-specific target forward. -/
structure PrimitiveTargetTransport
    (C : CoordinateSystem.{uAmbient, uBranch, uCoordinate, uObject, uPrimitive} P)
    (Target : P.Ambient -> Prop) where
  transport : forall {source target} (step : C.Primitive source target)
    (object : C.Object source),
    Target (C.realize source object) ->
      Target (C.realize target (C.act step object))

/-- Every primitive action transports a retained obstruction forward. -/
structure PrimitiveObstructionTransport
    (C : CoordinateSystem.{uAmbient, uBranch, uCoordinate, uObject, uPrimitive} P)
    (Obstruction : P.Ambient -> Type uObstruction) where
  transport : forall {source target} (step : C.Primitive source target)
    (object : C.Object source),
    Obstruction (C.realize source object) ->
      Obstruction (C.realize target (C.act step object))

/-- Primitive actions that preserve the represented ambient object up to the
registered semantic equivalence. -/
structure PrimitiveSemanticTransport
    (C : CoordinateSystem.{uAmbient, uBranch, uCoordinate, uObject, uPrimitive} P)
    (E : SemanticEquivalence P) where
  equivalent : forall {source target} (step : C.Primitive source target)
    (object : C.Object source),
    E.equivalent (C.realize source object)
      (C.realize target (C.act step object))

namespace CoordinatePath

/-- Baseline preservation composed over a complete coordinate path. -/
theorem transportBaseline (laws : PrimitiveBaselineTransport C)
    {source target : C.Coordinate} (path : CoordinatePath C source target)
    (object : C.Object source) (baseline : P.Baseline (C.realize source object)) :
    P.Baseline (C.realize target (path.run object)) := by
  induction path with
  | nil => exact baseline
  | cons step tail ih =>
      exact ih (C.act step object) (laws.preserves step object baseline)

/-- Branch-state transport composed over a complete coordinate path. -/
noncomputable def transportBranchState (laws : PrimitiveBranchStateTransport C)
    {source target : C.Coordinate} (path : CoordinatePath C source target)
    (object : C.Object source)
    (state : P.BranchState (C.realize source object)) :
    P.BranchState (C.realize target (path.run object)) := by
  induction path with
  | nil => exact state
  | cons step tail ih =>
      exact ih (C.act step object) (laws.transport step object state)

/-- Target transport composed over a complete coordinate path. -/
theorem transportTarget {Target : P.Ambient -> Prop}
    (laws : PrimitiveTargetTransport C Target)
    {source target : C.Coordinate} (path : CoordinatePath C source target)
    (object : C.Object source) (targetProof : Target (C.realize source object)) :
    Target (C.realize target (path.run object)) := by
  induction path with
  | nil => exact targetProof
  | cons step tail ih =>
      exact ih (C.act step object) (laws.transport step object targetProof)

/-- Retained-obstruction transport composed over a complete path. -/
noncomputable def transportObstruction {Obstruction : P.Ambient -> Type uObstruction}
    (laws : PrimitiveObstructionTransport C Obstruction)
    {source target : C.Coordinate} (path : CoordinatePath C source target)
    (object : C.Object source)
    (obstruction : Obstruction (C.realize source object)) :
    Obstruction (C.realize target (path.run object)) := by
  induction path with
  | nil => exact obstruction
  | cons step tail ih =>
      exact ih (C.act step object) (laws.transport step object obstruction)

/-- Semantic preservation composed over a complete path. -/
theorem semanticEquivalent {E : SemanticEquivalence P}
    (laws : PrimitiveSemanticTransport C E)
    {source target : C.Coordinate} (path : CoordinatePath C source target)
    (object : C.Object source) :
    E.equivalent (C.realize source object)
      (C.realize target (path.run object)) := by
  induction path with
  | nil => exact E.refl _
  | cons step tail ih =>
      exact E.trans (laws.equivalent step object) (ih (C.act step object))

end CoordinatePath

end Hypostructure.Core
