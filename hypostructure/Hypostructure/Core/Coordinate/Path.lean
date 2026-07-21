import Hypostructure.Core.Coordinate.System

/-!
# Framework-owned coordinate paths
-/

namespace Hypostructure.Core

universe uAmbient uBranch uCoordinate uObject uPrimitive

/-- The free category of primitive coordinate actions. -/
inductive CoordinatePath {P : Problem.{uAmbient, uBranch}}
    (C : CoordinateSystem.{uAmbient, uBranch, uCoordinate, uObject, uPrimitive} P) :
    C.Coordinate -> C.Coordinate -> Type (max uCoordinate uPrimitive)
  | nil : CoordinatePath C coordinate coordinate
  | cons (step : C.Primitive source middle)
      (tail : CoordinatePath C middle target) :
      CoordinatePath C source target

namespace CoordinatePath

variable {P : Problem.{uAmbient, uBranch}}
  {C : CoordinateSystem.{uAmbient, uBranch, uCoordinate, uObject, uPrimitive} P}

/-- Execute a path from left to right. -/
def run : {source target : C.Coordinate} ->
    CoordinatePath C source target -> C.Object source -> C.Object target
  | _, _, .nil, object => object
  | _, _, .cons step tail, object => tail.run (C.act step object)

/-- Concatenate two paths without exposing primitive action composition. -/
def append : {source middle target : C.Coordinate} ->
    CoordinatePath C source middle -> CoordinatePath C middle target ->
      CoordinatePath C source target
  | _, _, _, .nil, suffix => suffix
  | _, _, _, .cons step tail, suffix => .cons step (tail.append suffix)

/-- Number of primitive coordinate actions in a path. -/
def length : {source target : C.Coordinate} ->
    CoordinatePath C source target -> Nat
  | _, _, .nil => 0
  | _, _, .cons _ tail => tail.length + 1

@[simp] theorem run_nil {coordinate : C.Coordinate}
    (object : C.Object coordinate) :
    (CoordinatePath.nil (C := C)).run object = object :=
  rfl

@[simp] theorem run_cons {source middle target : C.Coordinate}
    (step : C.Primitive source middle) (tail : CoordinatePath C middle target)
    (object : C.Object source) :
    (CoordinatePath.cons step tail).run object = tail.run (C.act step object) :=
  rfl

@[simp] theorem nil_append {source target : C.Coordinate}
    (suffix : CoordinatePath C source target) :
    (CoordinatePath.nil (C := C)).append suffix = suffix :=
  rfl

@[simp] theorem append_nil {source target : C.Coordinate}
    (path : CoordinatePath C source target) :
    path.append CoordinatePath.nil = path := by
  induction path with
  | nil => rfl
  | cons step tail ih => simp [append, ih]

@[simp] theorem append_assoc {a b c d : C.Coordinate}
    (first : CoordinatePath C a b) (second : CoordinatePath C b c)
    (third : CoordinatePath C c d) :
    (first.append second).append third = first.append (second.append third) := by
  induction first with
  | nil => simp [append]
  | cons step tail ih => simp [append, ih]

@[simp] theorem run_append {source middle target : C.Coordinate}
    (first : CoordinatePath C source middle)
    (suffix : CoordinatePath C middle target) (object : C.Object source) :
    (first.append suffix).run object = suffix.run (first.run object) := by
  induction first with
  | nil => rfl
  | cons step tail ih => simp [append, run, ih]

@[simp] theorem length_append {source middle target : C.Coordinate}
    (first : CoordinatePath C source middle)
    (suffix : CoordinatePath C middle target) :
    (first.append suffix).length = first.length + suffix.length := by
  induction first with
  | nil => simp [append, length]
  | cons step tail ih => simp [append, length, ih, Nat.add_assoc, Nat.add_comm]

end CoordinatePath

end Hypostructure.Core
