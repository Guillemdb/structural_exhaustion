import Hypostructure.CT3.Automation
import Hypostructure.Graph.Response

/-!
# Graph specialization of CT3

Graph contributes only exact gluing and target-response semantics.  Candidate,
row, and coordinate schedules remain Core queries in `CT3.Capability`; this
module does not enumerate graphs or outside contexts and does not route an
outcome.
-/

namespace Hypostructure.Graph.CT3

open Hypostructure.Core

universe uPrevious u uContext uCoordinate uCandidate uRow

/-- Build domain-neutral CT3 semantics from exact same-boundary graph gluing. -/
noncomputable def targetSpec
    (Previous : Type uPrevious)
    {boundary : Boundary.{u}}
    (Target : FiniteObject.{u} -> Prop)
    (decideTarget : forall object, Decidable (Target object))
    (Context : Type uContext)
    (outside : Context -> OutsideContext boundary)
    (Coordinate : Type uCoordinate)
    (decode : Coordinate -> Context)
    (Candidate : Type uCandidate)
    (Row : Type uRow)
    (candidatePiece : Candidate -> BoundaryPiece boundary)
    (rowPiece : Row -> BoundaryPiece boundary)
    (rowResponse : Row -> Coordinate -> Bool)
    (Admissible : Previous -> BoundaryPiece boundary -> Candidate -> Prop)
    (StrictlySmaller : Previous -> BoundaryPiece boundary -> Candidate -> Prop) :
    _root_.Hypostructure.CT3.Spec Previous where
  Representative := BoundaryPiece boundary
  Candidate := Candidate
  Row := Row
  system := Graph.Response.targetSystem Target decideTarget Context outside
    Coordinate decode
  semantics := Graph.Response.targetSemantics Target decideTarget Context outside
    Coordinate decode
  candidatePiece := candidatePiece
  rowPiece := rowPiece
  rowResponse := rowResponse
  Admissible := Admissible
  StrictlySmaller := StrictlySmaller

/-- Exact realization of every semantic graph context supplies Core symbolic
coverage for any fixed pair of same-boundary pieces. -/
noncomputable def coverageOfExactContexts
    {boundary : Boundary.{u}}
    (Target : FiniteObject.{u} -> Prop)
    (decideTarget : forall object, Decidable (Target object))
    (Context : Type uContext)
    (outside : Context -> OutsideContext boundary)
    (Coordinate : Type uCoordinate)
    (decode : Coordinate -> Context)
    (representatives : Core.Response.Representatives (BoundaryPiece boundary))
    (coordinates : Core.Finite.Enumeration Coordinate)
    (complete : forall context, Exists fun index : Fin coordinates.card =>
      context = decode (coordinates.get index)) :
    Core.Response.FiniteTable.SymbolicCoverage
      (Graph.Response.targetSystem Target decideTarget Context outside Coordinate
        decode)
      representatives
      (Core.Response.FiniteTable.ExactSchedule.ofList coordinates.values) :=
  Graph.Response.coverageOfExactContexts representatives
    (Core.Response.FiniteTable.ExactSchedule.ofList coordinates.values) (by
      intro context
      obtain ⟨index, realized⟩ := complete context
      exact ⟨index, realized⟩)

section TargetTransport

variable {Previous : Type uPrevious}
  {boundary : Boundary.{u}}
  {Target : FiniteObject.{u} -> Prop}
  {decideTarget : forall object, Decidable (Target object)}
  {Context : Type uContext}
  {outside : Context -> OutsideContext boundary}
  {Coordinate : Type uCoordinate}
  {decode : Coordinate -> Context}
  {Candidate : Type uCandidate}
  {Row : Type uRow}
  {candidatePiece : Candidate -> BoundaryPiece boundary}
  {rowPiece : Row -> BoundaryPiece boundary}
  {rowResponse : Row -> Coordinate -> Bool}
  {Admissible : Previous -> BoundaryPiece boundary -> Candidate -> Prop}
  {StrictlySmaller : Previous -> BoundaryPiece boundary -> Candidate -> Prop}

local notation "graphSpec" =>
  targetSpec Previous Target decideTarget Context outside Coordinate decode
    Candidate Row candidatePiece rowPiece rowResponse Admissible StrictlySmaller

/-- A CT3 compression certificate transports the graph target through every
compatible outside context. -/
theorem compression_target_iff
    {capability : _root_.Hypostructure.CT3.Capability graphSpec}
    {previous : Previous}
    (certificate : _root_.Hypostructure.CT3.CompressionCertificate capability
      previous)
    (context : Context) :
    Target (Graph.glue (capability.sourceAt previous) (outside context)) ↔
      Target (Graph.glue (candidatePiece certificate.candidate)
        (outside context)) := by
  simpa [targetSpec] using certificate.target_iff context

/-- A validated known row transports the graph target through every compatible
outside context. -/
theorem knownRow_target_iff
    {capability : _root_.Hypostructure.CT3.Capability graphSpec}
    {previous : Previous}
    (table : _root_.Hypostructure.CT3.ExactTableState capability previous)
    (certificate : _root_.Hypostructure.CT3.KnownRowCertificate capability
      previous)
    (context : Context) :
    Target (Graph.glue (capability.sourceAt previous) (outside context)) ↔
      Target (Graph.glue (rowPiece certificate.row) (outside context)) := by
  simpa [targetSpec] using certificate.target_iff table context

end TargetTransport

end Hypostructure.Graph.CT3
