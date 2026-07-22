import Hypostructure.Core.Response.System
import Hypostructure.Core.Residual.Decision

/-!
# Exact finite response tables

Finite comparison scans only an explicit coordinate schedule supplied by the
literal predecessor ledger.  Core constructs both response vectors, selects
the first differing coordinate when one exists, and otherwise returns exact
neutrality.  A symbolic coverage theorem promotes finite neutrality to every
semantic context without enumerating an ambient context space.
-/

namespace Hypostructure.Core.Response.FiniteTable

open Hypostructure.Core

universe uRepresentative uContext uCoordinate uValue uPrevious

/-- The exact coordinate schedule owned by a residual.  Repetitions and order
are retained because a CT may assign semantic meaning to either. -/
structure ExactSchedule (Coordinate : Type uCoordinate) where
  coordinates : List Coordinate

namespace ExactSchedule

/-- Register a literal list as the complete finite schedule for one step. -/
def ofList {Coordinate : Type uCoordinate}
    (coordinates : List Coordinate) : ExactSchedule Coordinate :=
  ⟨coordinates⟩

@[simp] theorem ofList_coordinates {Coordinate : Type uCoordinate}
    (coordinates : List Coordinate) :
    (ofList coordinates).coordinates = coordinates :=
  rfl

end ExactSchedule

variable {Representative : Type uRepresentative}
  (system : Response.System.{uRepresentative, uContext, uCoordinate, uValue}
    Representative)

/-- An exact vector has one entry for each position in the supplied schedule. -/
abbrev ResponseVector (schedule : ExactSchedule system.Coordinate) :=
  Fin schedule.coordinates.length -> system.Value

/-- The framework-owned response table for two representatives. -/
structure Table (representatives : Response.Representatives Representative)
    (schedule : ExactSchedule system.Coordinate) where
  private mk ::
  sourceVector : ResponseVector system schedule
  replacementVector : ResponseVector system schedule
  sourceExact : forall index,
    sourceVector index = system.coordinateResponse representatives.source
      (schedule.coordinates.get index)
  replacementExact : forall index,
    replacementVector index =
      system.coordinateResponse representatives.replacement
        (schedule.coordinates.get index)

namespace Table

variable {system}
  {representatives : Response.Representatives Representative}
  {schedule : ExactSchedule system.Coordinate}

/-- Construct both exact response vectors from the registered evaluator. -/
def build (system : Response.System.{uRepresentative, uContext, uCoordinate,
      uValue} Representative)
    (representatives : Response.Representatives Representative)
    (schedule : ExactSchedule system.Coordinate) :
    Table system representatives schedule where
  sourceVector := fun index => system.coordinateResponse representatives.source
    (schedule.coordinates.get index)
  replacementVector := fun index =>
    system.coordinateResponse representatives.replacement
      (schedule.coordinates.get index)
  sourceExact := by intros; rfl
  replacementExact := by intros; rfl

@[simp] theorem build_sourceVector
    (index : Fin schedule.coordinates.length) :
    (build system representatives schedule).sourceVector index =
      system.coordinateResponse representatives.source
        (schedule.coordinates.get index) :=
  rfl

@[simp] theorem build_replacementVector
    (index : Fin schedule.coordinates.length) :
    (build system representatives schedule).replacementVector index =
      system.coordinateResponse representatives.replacement
        (schedule.coordinates.get index) :=
  rfl

end Table

variable {system}
  {representatives : Response.Representatives Representative}
  {schedule : ExactSchedule system.Coordinate}

/-- At least one scheduled coordinate distinguishes the representatives. -/
def Distinguishes (table : Table system representatives schedule) : Prop :=
  Exists fun index =>
    Not (table.sourceVector index = table.replacementVector index)

/-- Equality at every coordinate in the exact schedule. -/
structure Neutrality (table : Table system representatives schedule) : Prop where
  equalAt : forall index,
    table.sourceVector index = table.replacementVector index

/-- The earliest scheduled distinction, including equality of every preceding
entry. -/
structure FirstDistinction
    (table : Table system representatives schedule) where
  index : Fin schedule.coordinates.length
  differs : Not (table.sourceVector index = table.replacementVector index)
  earlierEqual : forall earlier, earlier < index ->
    table.sourceVector earlier = table.replacementVector earlier

namespace Table

variable (table : Table system representatives schedule)

private def valueAt? (vector : ResponseVector system schedule)
    (index : Nat) : Option system.Value :=
  if inBounds : index < schedule.coordinates.length then
    some (vector ⟨index, inBounds⟩)
  else
    none

private def mismatchAt (index : Nat) : Prop :=
  Not (valueAt? table.sourceVector index =
    valueAt? table.replacementVector index)

private instance [DecidableEq system.Value] :
    DecidablePred (mismatchAt table) :=
  fun _index => by
    unfold mismatchAt valueAt?
    infer_instance

/-- Core computes the first mismatch from any finite distinction proof. -/
def firstDistinction [DecidableEq system.Value]
    (distinguishes : Distinguishes table) : FirstDistinction table := by
  have existsMismatch : Exists (mismatchAt table) := by
    obtain ⟨index, differs⟩ := distinguishes
    refine ⟨index.val, ?_⟩
    simp [mismatchAt, valueAt?, index.isLt, differs]
  let first := Nat.find existsMismatch
  have firstMismatch : mismatchAt table first := Nat.find_spec existsMismatch
  have firstInBounds : first < schedule.coordinates.length := by
    by_contra outside
    simp [mismatchAt, valueAt?, outside] at firstMismatch
  refine {
    index := ⟨first, firstInBounds⟩
    differs := ?_
    earlierEqual := ?_
  }
  · simpa [mismatchAt, valueAt?, firstInBounds] using firstMismatch
  · intro earlier earlierBefore
    by_contra differs
    have earlierMismatch : mismatchAt table earlier.val := by
      simp [mismatchAt, valueAt?, earlier.isLt, differs]
    exact (Nat.find_min existsMismatch earlierBefore) earlierMismatch

/-- Absence of a distinction is promoted to exact finite neutrality. -/
def neutralityOfNotDistinguishes [DecidableEq system.Value]
    (absent : Not (Distinguishes table)) : Neutrality table where
  equalAt := by
    intro index
    exact match decEq (table.sourceVector index)
        (table.replacementVector index) with
      | .isTrue equal => equal
      | .isFalse differs => False.elim (absent ⟨index, differs⟩)

/-- Finite distinction is decidable from exact response values. -/
instance [DecidableEq system.Value] : Decidable (Distinguishes table) :=
  by
    unfold Distinguishes
    infer_instance

end Table

/-- Symbolic coverage of every semantic context by the exact schedule for the
two representatives under comparison.  This is a theorem over all contexts,
not an enumeration of them. -/
structure SymbolicCoverage
    (system : Response.System.{uRepresentative, uContext, uCoordinate, uValue}
      Representative)
    (representatives : Response.Representatives Representative)
    (schedule : ExactSchedule system.Coordinate) : Prop where
  locate : forall context, Exists fun index : Fin schedule.coordinates.length =>
    system.contextResponse representatives.source context =
        system.contextResponse representatives.source
          (system.decode (schedule.coordinates.get index)) /\
      system.contextResponse representatives.replacement context =
        system.contextResponse representatives.replacement
          (system.decode (schedule.coordinates.get index))

namespace SymbolicCoverage

/-- A one-coordinate schedule covers every semantic context whenever the
context type itself has at most one point.  This is domain-independent finite
coverage; applications provide only the coordinate. -/
def ofSubsingletonSingleton
    (system : Response.System.{uRepresentative, uContext, uCoordinate, uValue}
      Representative)
    (representatives : Response.Representatives Representative)
    [Subsingleton system.Context] (coordinate : system.Coordinate) :
    SymbolicCoverage system representatives
      (ExactSchedule.ofList [coordinate]) where
  locate := by
    intro context
    refine ⟨⟨0, by simp⟩, ?_, ?_⟩
    · rw [Subsingleton.elim context (system.decode coordinate)]
      simp [ExactSchedule.ofList]
    · rw [Subsingleton.elim context (system.decode coordinate)]
      simp [ExactSchedule.ofList]

end SymbolicCoverage

namespace Neutrality

variable {table : Table system representatives schedule}

/-- Exact finite neutrality plus symbolic coverage yields universal semantic
neutrality. -/
def universal (neutral : Neutrality table)
    (coverage : SymbolicCoverage system representatives schedule) :
    Response.UniversalNeutrality system representatives where
  equalInContext := by
    intro context
    obtain ⟨index, sourceCovered, replacementCovered⟩ :=
      coverage.locate context
    calc
      system.contextResponse representatives.source context =
          system.contextResponse representatives.source
            (system.decode (schedule.coordinates.get index)) := sourceCovered
      _ = system.coordinateResponse representatives.source
            (schedule.coordinates.get index) :=
          (system.coordinateExact representatives.source _).symm
      _ = table.sourceVector index := (table.sourceExact index).symm
      _ = table.replacementVector index := neutral.equalAt index
      _ = system.coordinateResponse representatives.replacement
            (schedule.coordinates.get index) := table.replacementExact index
      _ = system.contextResponse representatives.replacement
            (system.decode (schedule.coordinates.get index)) :=
          system.coordinateExact representatives.replacement _
      _ = system.contextResponse representatives.replacement context :=
          replacementCovered.symm

/-- Exact finite neutrality becomes target-complete equivalence only after
symbolic coverage and exact target semantics have both been registered. -/
def targetComplete (neutral : Neutrality table)
    (coverage : SymbolicCoverage system representatives schedule)
    (semantics : Response.TargetSemantics system) :
    Response.TargetCompleteEquivalence semantics representatives :=
  (neutral.universal coverage).targetComplete semantics

end Neutrality

section LedgerExecution

variable (system)
  (representatives : Response.Representatives Representative)

/-- Framework-owned finite classification over a schedule queried from the
literal predecessor ledger.  Applications supply the query and response laws;
Core constructs the table and selects the decision constructor. -/
def classificationNode [DecidableEq system.Value]
    {Previous : Sort uPrevious}
    (scheduleQuery : Residual.Query Previous
      (fun _previous => ExactSchedule system.Coordinate)) :
    Residual.Decision.Node Previous
      (fun previous => Distinguishes
        (Table.build system representatives (scheduleQuery.read previous)))
      (fun previous => Neutrality
        (Table.build system representatives (scheduleQuery.read previous))) :=
  Residual.Decision.Node.create
    (fun _previous => inferInstance)
    (fun previous absent =>
      (Table.build system representatives
        (scheduleQuery.read previous)).neutralityOfNotDistinguishes absent)

/-- Execute exact finite response classification while retaining the complete
incoming ledger as the decision stage's literal predecessor. -/
def run [DecidableEq system.Value]
    {Previous : Sort uPrevious}
    (scheduleQuery : Residual.Query Previous
      (fun _previous => ExactSchedule system.Coordinate))
    (previous : Previous) :
    Residual.Decision.Stage
      (fun current => Distinguishes
        (Table.build system representatives (scheduleQuery.read current)))
      (fun current => Neutrality
        (Table.build system representatives (scheduleQuery.read current))) :=
  (classificationNode system representatives scheduleQuery).run previous

end LedgerExecution

end Hypostructure.Core.Response.FiniteTable
