import Hypostructure.Graph.CT3
import Hypostructure.Fixtures.GraphResponse

/-!
# CT3 vertical-slice fixtures

The neutral fixture reaches all four terminals from residual-owned schedules.
The graph fixture compares two same-boundary pieces using the existing exact
gluing semantics and transports an isomorphism-invariant target.
-/

namespace Hypostructure.Fixtures.CT3

namespace Neutral

open Hypostructure.Core

/-- A stored row names its representative and its two exact Boolean entries. -/
structure Row where
  piece : Bool
  atFalse : Bool
  atTrue : Bool
  deriving DecidableEq, Repr

def rowResponse (row : Row) (coordinate : Bool) : Bool :=
  if coordinate then row.atTrue else row.atFalse

def response (piece context : Bool) : Bool :=
  decide (piece = context)

abbrev responseSystem : Core.Response.System Bool :=
  Core.Response.System.ofDecodedContexts Bool Bool Bool response id

def targetMeaning : Core.Response.TargetSemantics responseSystem where
  TargetResponse := fun piece context => piece = context
  Accepts := fun value => value = true
  target_iff_accepts := by
    intro piece context
    change piece = context ↔ response piece context = true
    simp [response]

/-- Literal residual carrying all finite CT3 schedules. -/
structure Residual where
  source : Bool
  coordinates : Core.Finite.Enumeration Bool
  candidates : Core.Finite.Enumeration Bool
  rows : Core.Finite.Enumeration Row
  admissible : Bool -> Bool
  smaller : Bool -> Bool
  coordinatesComplete : forall coordinate, coordinate ∈ coordinates.values
  work_le_eight : _root_.Hypostructure.CT3.localCheckBound coordinates candidates
    rows <= 8

abbrev Previous := Core.Residual.Ledger Residual

abbrev spec : _root_.Hypostructure.CT3.Spec Previous where
  Representative := Bool
  Candidate := Bool
  Row := Row
  system := responseSystem
  semantics := targetMeaning
  candidatePiece := id
  rowPiece := Row.piece
  rowResponse := rowResponse
  Admissible := fun previous _source candidate =>
    (Core.Residual.residualOf previous).admissible candidate = true
  StrictlySmaller := fun previous _source candidate =>
    (Core.Residual.residualOf previous).smaller candidate = true

def residualQuery : Core.Residual.Query Previous fun _previous => Residual :=
  Core.Residual.Query.residual

def sourceQuery : Core.Residual.Query Previous fun _previous => Bool :=
  residualQuery.map fun _previous residual => residual.source

def coordinateQuery : Core.Residual.Query Previous fun _previous =>
    Core.Finite.Enumeration Bool :=
  residualQuery.map fun _previous residual => residual.coordinates

def candidateQuery : Core.Residual.Query Previous fun _previous =>
    Core.Finite.Enumeration Bool :=
  residualQuery.map fun _previous residual => residual.candidates

def rowQuery : Core.Residual.Query Previous fun _previous =>
    Core.Finite.Enumeration Row :=
  residualQuery.map fun _previous residual => residual.rows

/-- Symbolic coverage is derived from completeness of the queried coordinate
schedule, not from a global `FinEnum Bool` instance. -/
def coverage (previous : Previous) (replacement : Bool) :
    Core.Response.FiniteTable.SymbolicCoverage responseSystem
      (spec.representatives (sourceQuery.read previous) replacement)
      (Core.Response.FiniteTable.ExactSchedule.ofList
        (coordinateQuery.read previous).values) where
  locate := by
    intro context
    change Bool at context
    have complete : context ∈ (coordinateQuery.read previous).values := by
      simpa [coordinateQuery, residualQuery] using
        (Core.Residual.residualOf previous).coordinatesComplete context
    obtain ⟨index, rfl⟩ :=
      ((coordinateQuery.read previous).mem_iff_exists_index context).mp
        complete
    exact ⟨index, rfl, rfl⟩

def capability : _root_.Hypostructure.CT3.Capability spec where
  source := sourceQuery
  coordinates := coordinateQuery
  candidates := candidateQuery
  rows := rowQuery
  valueDecEq := by
    change DecidableEq Bool
    infer_instance
  admissibleDecidable := fun previous _source candidate =>
    Bool.decEq ((Core.Residual.residualOf previous).admissible candidate) true
  smallerDecidable := fun previous _source candidate =>
    Bool.decEq ((Core.Residual.residualOf previous).smaller candidate) true
  candidateCoverage := fun previous candidate _member => coverage previous candidate
  rowCoverage := fun previous row _member => coverage previous row.piece
  inputSize := fun _previous => 0
  workCoefficient := 8
  workDegree := 0
  workBound := fun previous => by
    change _root_.Hypostructure.CT3.localCheckBound
      (Core.Residual.residualOf previous).coordinates
      (Core.Residual.residualOf previous).candidates
      (Core.Residual.residualOf previous).rows <= 8
    exact (Core.Residual.residualOf previous).work_le_eight

def boolCoordinates : Core.Finite.Enumeration Bool :=
  Core.Finite.Enumeration.ofNodupList [false, true] (by decide)

theorem boolCoordinates_complete (coordinate : Bool) :
    coordinate ∈ boolCoordinates.values := by
  change coordinate ∈ [false, true]
  cases coordinate <;> simp

def exactFalseRow : Row := ⟨false, true, false⟩
def exactTrueRow : Row := ⟨true, false, true⟩
def defectiveFalseRow : Row := ⟨false, false, false⟩

def compressionResidual : Residual where
  source := false
  coordinates := boolCoordinates
  candidates := Core.Finite.Enumeration.singleton false
  rows := Core.Finite.Enumeration.empty Row
  admissible := fun _candidate => true
  smaller := fun _candidate => true
  coordinatesComplete := boolCoordinates_complete
  work_le_eight := by decide

def compressionPrevious : Previous :=
  Core.Residual.Ledger.initial compressionResidual

def compressionResult : _root_.Hypostructure.CT3.ExecutionResult spec capability :=
  _root_.Hypostructure.CT3.execute spec capability compressionPrevious

theorem compression_previous :
    compressionResult.stage.previous = compressionPrevious := rfl

theorem compression_terminal :
    compressionResult.terminal = .compression := by decide

theorem compression_checks : compressionResult.checks = 4 := by decide

theorem compression_trace :
    compressionResult.traceNodes =
      [.entry, .vectorComputation, .compressionSearch, .compressionTerminal] :=
  by decide

theorem compression_verified :
    _root_.Hypostructure.CT3.OutcomeClaim compressionResult.outcome :=
  compressionResult.verified

def distinguishingResidual : Residual where
  source := false
  coordinates := boolCoordinates
  candidates := Core.Finite.Enumeration.empty Bool
  rows := Core.Finite.Enumeration.singleton defectiveFalseRow
  admissible := fun _candidate => false
  smaller := fun _candidate => false
  coordinatesComplete := boolCoordinates_complete
  work_le_eight := by decide

def distinguishingPrevious : Previous :=
  Core.Residual.Ledger.initial distinguishingResidual

def distinguishingResult :
    _root_.Hypostructure.CT3.ExecutionResult spec capability :=
  _root_.Hypostructure.CT3.execute spec capability distinguishingPrevious

theorem distinguishing_terminal :
    distinguishingResult.terminal = .distinguishing := by decide

theorem distinguishing_checks : distinguishingResult.checks = 1 := by decide

theorem distinguishing_trace :
    distinguishingResult.traceNodes =
      [.entry, .vectorComputation, .compressionSearch, .tableValidation,
        .distinguishingTerminal] :=
  by decide

theorem distinguishing_verified :
    _root_.Hypostructure.CT3.OutcomeClaim distinguishingResult.outcome :=
  distinguishingResult.verified

def knownRowResidual : Residual where
  source := false
  coordinates := boolCoordinates
  candidates := Core.Finite.Enumeration.empty Bool
  rows := Core.Finite.Enumeration.singleton exactFalseRow
  admissible := fun _candidate => false
  smaller := fun _candidate => false
  coordinatesComplete := boolCoordinates_complete
  work_le_eight := by decide

def knownRowPrevious : Previous :=
  Core.Residual.Ledger.initial knownRowResidual

def knownRowResult : _root_.Hypostructure.CT3.ExecutionResult spec capability :=
  _root_.Hypostructure.CT3.execute spec capability knownRowPrevious

theorem knownRow_terminal : knownRowResult.terminal = .knownRow := by decide

theorem knownRow_checks : knownRowResult.checks = 4 := by decide

theorem knownRow_trace :
    knownRowResult.traceNodes =
      [.entry, .vectorComputation, .compressionSearch, .tableValidation,
        .rowLookup, .knownRowTerminal] :=
  by decide

theorem knownRow_verified :
    _root_.Hypostructure.CT3.OutcomeClaim knownRowResult.outcome :=
  knownRowResult.verified

def novelRowResidual : Residual where
  source := false
  coordinates := boolCoordinates
  candidates := Core.Finite.Enumeration.empty Bool
  rows := Core.Finite.Enumeration.singleton exactTrueRow
  admissible := fun _candidate => false
  smaller := fun _candidate => false
  coordinatesComplete := boolCoordinates_complete
  work_le_eight := by decide

def novelRowPrevious : Previous :=
  Core.Residual.Ledger.initial novelRowResidual

def novelRowResult : _root_.Hypostructure.CT3.ExecutionResult spec capability :=
  _root_.Hypostructure.CT3.execute spec capability novelRowPrevious

theorem novelRow_terminal : novelRowResult.terminal = .novelRow := by decide

theorem novelRow_checks : novelRowResult.checks = 4 := by decide

theorem novelRow_trace :
    novelRowResult.traceNodes =
      [.entry, .vectorComputation, .compressionSearch, .tableValidation,
        .rowLookup, .novelRowTerminal] :=
  by decide

theorem novelRow_verified :
    _root_.Hypostructure.CT3.OutcomeClaim novelRowResult.outcome :=
  novelRowResult.verified

theorem compression_work :
    compressionResult.checks <= capability.workCoefficient *
      (capability.inputSize compressionPrevious + 1) ^ capability.workDegree :=
  compressionResult.checks_le_polynomial

theorem novelRow_work :
    novelRowResult.checks <= capability.workCoefficient *
      (capability.inputSize novelRowPrevious + 1) ^ capability.workDegree :=
  novelRowResult.checks_le_polynomial

end Neutral

namespace Graph

open Hypostructure.Core
open Hypostructure.Graph

structure Residual where
  coordinates : Core.Finite.Enumeration Bool
  candidates : Core.Finite.Enumeration Unit
  rows : Core.Finite.Enumeration Unit
  coordinatesComplete : forall coordinate, coordinate ∈ coordinates.values
  work_le_eight : _root_.Hypostructure.CT3.localCheckBound coordinates candidates
    rows <= 8

abbrev Previous := Core.Residual.Ledger Residual

noncomputable abbrev spec :=
  _root_.Hypostructure.Graph.CT3.targetSpec Previous
    Hypostructure.Fixtures.GraphResponse.HasThreeVertices
    Hypostructure.Fixtures.GraphResponse.hasThreeVerticesDecidable Bool
    Hypostructure.Fixtures.GraphResponse.outsideByCode Bool id Unit Unit
    (fun _candidate => Hypostructure.Fixtures.GraphResponse.emptyPiece)
    (fun _row => Hypostructure.Fixtures.GraphResponse.emptyPiece)
    (fun _row coordinate =>
      Hypostructure.Fixtures.GraphResponse.sizeResponses.coordinateResponse
        Hypostructure.Fixtures.GraphResponse.emptyPiece coordinate)
    (fun _previous _source _candidate => True)
    (fun _previous _source _candidate => True)

def residualQuery : Core.Residual.Query Previous fun _previous => Residual :=
  Core.Residual.Query.residual

noncomputable def sourceQuery : Core.Residual.Query Previous fun _previous =>
    spec.Representative :=
  residualQuery.map fun _previous _residual =>
    Hypostructure.Fixtures.GraphResponse.edgePiece

def coordinateQuery : Core.Residual.Query Previous fun _previous =>
    Core.Finite.Enumeration Bool :=
  residualQuery.map fun _previous residual => residual.coordinates

def candidateQuery : Core.Residual.Query Previous fun _previous =>
    Core.Finite.Enumeration Unit :=
  residualQuery.map fun _previous residual => residual.candidates

def rowQuery : Core.Residual.Query Previous fun _previous =>
    Core.Finite.Enumeration Unit :=
  residualQuery.map fun _previous residual => residual.rows

noncomputable def capability : _root_.Hypostructure.CT3.Capability spec where
  source := sourceQuery
  coordinates := coordinateQuery
  candidates := candidateQuery
  rows := rowQuery
  valueDecEq := by
    change DecidableEq Bool
    infer_instance
  admissibleDecidable := fun _previous _source _candidate => by
    change Decidable True
    infer_instance
  smallerDecidable := fun _previous _source _candidate => by
    change Decidable True
    infer_instance
  candidateCoverage := by
    intro previous candidate _member
    apply _root_.Hypostructure.Graph.CT3.coverageOfExactContexts
      Hypostructure.Fixtures.GraphResponse.HasThreeVertices
      Hypostructure.Fixtures.GraphResponse.hasThreeVerticesDecidable Bool
      Hypostructure.Fixtures.GraphResponse.outsideByCode Bool id
    intro context
    have complete : context ∈ (coordinateQuery.read previous).values := by
      change context ∈ (Core.Residual.residualOf previous).coordinates.values
      exact (Core.Residual.residualOf previous).coordinatesComplete context
    obtain ⟨index, indexed⟩ :=
      ((coordinateQuery.read previous).mem_iff_exists_index context).mp
        complete
    exact ⟨index, indexed.symm⟩
  rowCoverage := by
    intro previous row _member
    apply _root_.Hypostructure.Graph.CT3.coverageOfExactContexts
      Hypostructure.Fixtures.GraphResponse.HasThreeVertices
      Hypostructure.Fixtures.GraphResponse.hasThreeVerticesDecidable Bool
      Hypostructure.Fixtures.GraphResponse.outsideByCode Bool id
    intro context
    have complete : context ∈ (coordinateQuery.read previous).values := by
      change context ∈ (Core.Residual.residualOf previous).coordinates.values
      exact (Core.Residual.residualOf previous).coordinatesComplete context
    obtain ⟨index, indexed⟩ :=
      ((coordinateQuery.read previous).mem_iff_exists_index context).mp
        complete
    exact ⟨index, indexed.symm⟩
  inputSize := fun _previous => 0
  workCoefficient := 8
  workDegree := 0
  workBound := fun previous => by
    change _root_.Hypostructure.CT3.localCheckBound
      (Core.Residual.residualOf previous).coordinates
      (Core.Residual.residualOf previous).candidates
      (Core.Residual.residualOf previous).rows <= 8
    exact (Core.Residual.residualOf previous).work_le_eight

def residual : Residual where
  coordinates := Neutral.boolCoordinates
  candidates := Core.Finite.Enumeration.singleton ()
  rows := Core.Finite.Enumeration.singleton ()
  coordinatesComplete := Neutral.boolCoordinates_complete
  work_le_eight := by decide

noncomputable def previous : Previous := Core.Residual.Ledger.initial residual

theorem candidate_compresses :
    _root_.Hypostructure.CT3.Compresses capability previous () := by
  refine ⟨trivial, trivial, ?_⟩
  change _root_.Hypostructure.CT3.ScheduleNeutrality capability previous
    Hypostructure.Fixtures.GraphResponse.emptyPiece
  refine { equalAt := ?_ }
  intro index
  rw [(_root_.Hypostructure.CT3.responseTableAt capability previous
      Hypostructure.Fixtures.GraphResponse.emptyPiece).sourceExact]
  rw [(_root_.Hypostructure.CT3.responseTableAt capability previous
      Hypostructure.Fixtures.GraphResponse.emptyPiece).replacementExact]
  change Hypostructure.Fixtures.GraphResponse.sizeResponses.coordinateResponse
      Hypostructure.Fixtures.GraphResponse.edgePiece _ =
    Hypostructure.Fixtures.GraphResponse.sizeResponses.coordinateResponse
      Hypostructure.Fixtures.GraphResponse.emptyPiece _
  exact (Hypostructure.Fixtures.GraphResponse.size_source_coordinate_true _).trans
    (Hypostructure.Fixtures.GraphResponse.size_replacement_coordinate_true _).symm

theorem candidate_scheduled :
    () ∈ (capability.candidatesAt previous).values := by
  change () ∈ [()]
  simp

theorem sourceAt_previous :
    capability.sourceAt previous =
      Hypostructure.Fixtures.GraphResponse.edgePiece :=
  rfl

noncomputable def result :
    _root_.Hypostructure.CT3.ExecutionResult spec capability :=
  _root_.Hypostructure.CT3.execute spec capability previous

theorem result_previous : result.stage.previous = previous := rfl

theorem result_terminal : result.terminal = .compression :=
  result.terminal_compression_of_exists
    ⟨(), candidate_scheduled, candidate_compresses⟩

theorem compression_has_hit :
    (_root_.Hypostructure.CT3.compressionScan capability previous).HasHit :=
  Core.Finite.Search.complete (capability.candidatesAt previous)
    (_root_.Hypostructure.CT3.Compresses capability previous)
    (_root_.Hypostructure.CT3.compressesDecidable capability previous)
    ⟨(), candidate_scheduled, candidate_compresses⟩

noncomputable def certificate :
    _root_.Hypostructure.CT3.CompressionCertificate capability previous :=
  (_root_.Hypostructure.CT3.compressionScan capability previous).hitOfHasHit
    compression_has_hit

theorem target_transport (context : Bool) :
    Hypostructure.Fixtures.GraphResponse.HasThreeVertices
        (Hypostructure.Graph.glue
          Hypostructure.Fixtures.GraphResponse.edgePiece
          (Hypostructure.Fixtures.GraphResponse.outsideByCode context)) ↔
      Hypostructure.Fixtures.GraphResponse.HasThreeVertices
        (Hypostructure.Graph.glue
          Hypostructure.Fixtures.GraphResponse.emptyPiece
          (Hypostructure.Fixtures.GraphResponse.outsideByCode context)) := by
  simpa only [sourceAt_previous]
    using _root_.Hypostructure.Graph.CT3.compression_target_iff
      (certificate := certificate) context

theorem result_work :
    result.checks <= capability.workCoefficient *
      (capability.inputSize previous + 1) ^ capability.workDegree :=
  result.checks_le_polynomial

end Graph

#print axioms Neutral.compression_terminal
#print axioms Neutral.compression_checks
#print axioms Neutral.compression_verified
#print axioms Neutral.distinguishing_terminal
#print axioms Neutral.distinguishing_checks
#print axioms Neutral.distinguishing_verified
#print axioms Neutral.knownRow_terminal
#print axioms Neutral.knownRow_checks
#print axioms Neutral.knownRow_verified
#print axioms Neutral.novelRow_terminal
#print axioms Neutral.novelRow_checks
#print axioms Neutral.novelRow_verified
#print axioms Graph.result_terminal
#print axioms Graph.target_transport

end Hypostructure.Fixtures.CT3
