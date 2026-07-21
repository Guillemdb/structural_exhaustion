import Hypostructure.CT3.Spec

/-!
# CT3 queried capability

Every finite family is read through a typed query from the one literal
predecessor.  Symbolic coverage is a theorem about those exact queried
coordinates; it is not an ambient enumeration.
-/

namespace Hypostructure.CT3

universe uPrevious uRepresentative uContext uCoordinate uValue uCandidate uRow

/-- Exact worst-case primitive checks in the prescribed CT3 schedule. -/
def localCheckBound
    {Coordinate : Type uCoordinate} {Candidate : Type uCandidate}
    {Row : Type uRow}
    (coordinates : Core.Finite.Enumeration Coordinate)
    (candidates : Core.Finite.Enumeration Candidate)
    (rows : Core.Finite.Enumeration Row) : Nat :=
  candidates.card * (2 + coordinates.card) +
    rows.card * coordinates.card + rows.card * coordinates.card

/-- The check bound is the manuscript formula
`candidates * (2 + coordinates) + 2 * rows * coordinates`. -/
theorem localCheckBound_eq_formula
    {Coordinate : Type uCoordinate} {Candidate : Type uCandidate}
    {Row : Type uRow}
    (coordinates : Core.Finite.Enumeration Coordinate)
    (candidates : Core.Finite.Enumeration Candidate)
    (rows : Core.Finite.Enumeration Row) :
    localCheckBound coordinates candidates rows =
      candidates.card * (2 + coordinates.card) +
        2 * rows.card * coordinates.card := by
  simp [localCheckBound, two_mul, Nat.add_mul, Nat.add_assoc]

/-- Minimum executable capability for CT3.

The four schedules and the source representative are typed reads from the
same predecessor.  Coverage is required only for scheduled candidates and
rows, so the capability does not quantify over an ambient representative
universe. -/
structure Capability {Previous : Type uPrevious}
    (spec : Spec.{uPrevious, uRepresentative, uContext, uCoordinate, uValue,
      uCandidate, uRow} Previous) where
  source : Core.Residual.Query Previous fun _previous => spec.Representative
  coordinates : Core.Residual.Query Previous fun _previous =>
    Core.Finite.Enumeration spec.system.Coordinate
  candidates : Core.Residual.Query Previous fun _previous =>
    Core.Finite.Enumeration spec.Candidate
  rows : Core.Residual.Query Previous fun _previous =>
    Core.Finite.Enumeration spec.Row
  valueDecEq : DecidableEq spec.system.Value
  admissibleDecidable : (previous : Previous) -> (source : spec.Representative) ->
    (candidate : spec.Candidate) ->
      Decidable (spec.Admissible previous source candidate)
  smallerDecidable : (previous : Previous) -> (source : spec.Representative) ->
    (candidate : spec.Candidate) ->
      Decidable (spec.StrictlySmaller previous source candidate)
  candidateCoverage : (previous : Previous) -> (candidate : spec.Candidate) ->
    candidate ∈ (candidates.read previous).values ->
      Core.Response.FiniteTable.SymbolicCoverage spec.system
        (spec.representatives (source.read previous)
          (spec.candidatePiece candidate))
        (Core.Response.FiniteTable.ExactSchedule.ofList
          (coordinates.read previous).values)
  rowCoverage : (previous : Previous) -> (row : spec.Row) ->
    row ∈ (rows.read previous).values ->
      Core.Response.FiniteTable.SymbolicCoverage spec.system
        (spec.representatives (source.read previous) (spec.rowPiece row))
        (Core.Response.FiniteTable.ExactSchedule.ofList
          (coordinates.read previous).values)
  inputSize : Previous -> Nat
  workCoefficient : Nat
  workDegree : Nat
  workBound : forall previous,
    localCheckBound (coordinates.read previous) (candidates.read previous)
      (rows.read previous) <=
        workCoefficient * (inputSize previous + 1) ^ workDegree

namespace Capability

variable {Previous : Type uPrevious}
  {spec : Spec.{uPrevious, uRepresentative, uContext, uCoordinate, uValue,
    uCandidate, uRow} Previous}

/-- Source representative retrieved from the exact predecessor. -/
def sourceAt (capability : Capability spec) (previous : Previous) :
    spec.Representative :=
  capability.source.read previous

/-- Exact coordinate schedule retrieved from the exact predecessor. -/
def coordinatesAt (capability : Capability spec) (previous : Previous) :
    Core.Finite.Enumeration spec.system.Coordinate :=
  capability.coordinates.read previous

/-- Exact candidate schedule retrieved from the exact predecessor. -/
def candidatesAt (capability : Capability spec) (previous : Previous) :
    Core.Finite.Enumeration spec.Candidate :=
  capability.candidates.read previous

/-- Exact row schedule retrieved from the exact predecessor. -/
def rowsAt (capability : Capability spec) (previous : Previous) :
    Core.Finite.Enumeration spec.Row :=
  capability.rows.read previous

/-- Core's exact response-table schedule for the queried coordinates. -/
def exactScheduleAt (capability : Capability spec) (previous : Previous) :
    Core.Response.FiniteTable.ExactSchedule spec.system.Coordinate :=
  Core.Response.FiniteTable.ExactSchedule.ofList
    (capability.coordinatesAt previous).values

/-- Framework-visible polynomial budget for the complete CT3 schedule. -/
def polynomialBudget (capability : Capability spec) :
    Core.PolynomialCheckBudget Previous where
  size := capability.inputSize
  checks := fun previous => localCheckBound (capability.coordinatesAt previous)
    (capability.candidatesAt previous) (capability.rowsAt previous)
  coefficient := capability.workCoefficient
  degree := capability.workDegree
  bounded := capability.workBound

end Capability

end Hypostructure.CT3
