import Hypostructure.CT3.Automation
import Hypostructure.CT3.ResidualRoute
import Hypostructure.CT3.RunSchedule
import Hypostructure.CT3.SameInterface
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
universe uFocusPrevious uItem uGood uResidual uInput uOutcome uTrace

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

/-! ## Scheduled bounded-entry execution -/

/-- Graph adapter for the CT3-owned scheduled executor.  Graph supplies no
table plumbing or routing here: the caller provides the registered graph CT3
spec/capability and the residual-owned item-to-input query, and CT3 derives
the per-item terminal schedule. -/
noncomputable def focusedRunSchedule {FocusPrevious : Sort uFocusPrevious}
    {focus : Core.Residual.Focus.Profile FocusPrevious}
    {Previous : Type uPrevious}
    (spec : _root_.Hypostructure.CT3.Spec.{uPrevious, u, uContext,
      uCoordinate, 0, uCandidate, uRow} Previous)
    (capability : _root_.Hypostructure.CT3.Capability spec)
    (Item : Type uItem)
    (items :
      Core.Residual.Focus.ActiveQuery focus fun _previous _active =>
        Core.Finite.Enumeration Item)
    (input :
      Core.Residual.Focus.ActiveQuery focus fun _previous _active =>
        Item -> Previous) :
    _root_.Hypostructure.CT3.Schedule.FocusedContract focus :=
  _root_.Hypostructure.CT3.RunSchedule.focused spec capability Item items input

/-- Retrieve the exact per-item graph CT3 result through the same active
residual query used by the scheduled terminal executor. -/
noncomputable def focusedRunResultAt {FocusPrevious : Sort uFocusPrevious}
    {focus : Core.Residual.Focus.Profile FocusPrevious}
    {Previous : Type uPrevious}
    (spec : _root_.Hypostructure.CT3.Spec.{uPrevious, u, uContext,
      uCoordinate, 0, uCandidate, uRow} Previous)
    (capability : _root_.Hypostructure.CT3.Capability spec)
    (Item : Type uItem)
    (input :
      Core.Residual.Focus.ActiveQuery focus fun _previous _active =>
        Item -> Previous) :
    Core.Residual.Focus.ActiveQuery focus fun _previous _active =>
      Item -> _root_.Hypostructure.CT3.ExecutionResult spec capability :=
  _root_.Hypostructure.CT3.RunSchedule.resultAt spec capability Item input

/-- Execute graph scheduled CT3 and terminal classification in one
framework-owned call. -/
noncomputable def runFocusedClassified {FocusPrevious : Sort uFocusPrevious}
    {focus : Core.Residual.Focus.Profile FocusPrevious}
    {Previous : Type uPrevious}
    (spec : _root_.Hypostructure.CT3.Spec.{uPrevious, u, uContext,
      uCoordinate, 0, uCandidate, uRow} Previous)
    (capability : _root_.Hypostructure.CT3.Capability spec)
    (Item : Type uItem)
    (items :
      Core.Residual.Focus.ActiveQuery focus fun _previous _active =>
        Core.Finite.Enumeration Item)
    (input :
      Core.Residual.Focus.ActiveQuery focus fun _previous _active =>
        Item -> Previous)
    (previous : FocusPrevious) :
    (focusedRunSchedule spec capability Item items input).Stage :=
  _root_.Hypostructure.CT3.RunSchedule.runClassified spec capability Item
    items input previous

@[simp] theorem runFocusedClassified_previous
    {FocusPrevious : Sort uFocusPrevious}
    {focus : Core.Residual.Focus.Profile FocusPrevious}
    {Previous : Type uPrevious}
    (spec : _root_.Hypostructure.CT3.Spec.{uPrevious, u, uContext,
      uCoordinate, 0, uCandidate, uRow} Previous)
    (capability : _root_.Hypostructure.CT3.Capability spec)
    (Item : Type uItem)
    (items :
      Core.Residual.Focus.ActiveQuery focus fun _previous _active =>
        Core.Finite.Enumeration Item)
    (input :
      Core.Residual.Focus.ActiveQuery focus fun _previous _active =>
        Item -> Previous)
    (previous : FocusPrevious) :
    (runFocusedClassified spec capability Item items input previous).previous =
      previous :=
  _root_.Hypostructure.CT3.RunSchedule.runClassified_previous spec capability
    Item items input previous

/-! ## Same-interface registration from classified CT3 schedules -/

/-- Graph adapter for CT3-owned all-good same-interface registration after
schedule classification.  Graph supplies no package routing; the package
contract is the generic CT3/Core contract. -/
noncomputable def registerClassifiedSameInterface
    {FocusPrevious : Sort uFocusPrevious}
    {focus : Core.Residual.Focus.Profile FocusPrevious}
    {schedule :
      _root_.Hypostructure.CT3.Schedule.FocusedContract.{uFocusPrevious,
        uItem} focus}
    (contract :
      _root_.Hypostructure.CT3.SameInterface.PackageContract.{uFocusPrevious,
        uItem, uGood, uResidual} schedule)
    (previous : FocusPrevious) :
    (contract.sameInterfaceContract).Stage :=
  contract.registerClassified previous

@[simp] theorem registerClassifiedSameInterface_source_previous
    {FocusPrevious : Sort uFocusPrevious}
    {focus : Core.Residual.Focus.Profile FocusPrevious}
    {schedule :
      _root_.Hypostructure.CT3.Schedule.FocusedContract.{uFocusPrevious,
        uItem} focus}
    (contract :
      _root_.Hypostructure.CT3.SameInterface.PackageContract.{uFocusPrevious,
        uItem, uGood, uResidual} schedule)
    (previous : FocusPrevious) :
    (registerClassifiedSameInterface contract previous).previous.previous =
      previous :=
  contract.registerClassified_source_previous previous

/-! ## Residual routing from classified CT3 schedules -/

/-- Graph adapter for CT3-owned first-residual routing after schedule
classification.  Graph supplies no routing logic; the route contract is the
generic CT3/Core residual route contract. -/
noncomputable def advanceClassifiedResidualRoute
    {FocusPrevious : Type uFocusPrevious}
    {focus : Core.Residual.Focus.Profile FocusPrevious}
    {schedule :
      _root_.Hypostructure.CT3.Schedule.FocusedContract.{uFocusPrevious + 1,
        uItem} focus}
    (contract :
      _root_.Hypostructure.CT3.ResidualRoute.Contract.{uFocusPrevious, uItem,
        uGood, uResidual, uInput, uOutcome, uTrace} schedule)
    (edge : Core.Routing.Edge) (previous : FocusPrevious) :
    Core.Routing.Stage (contract.transition edge) :=
  contract.advanceClassified edge previous

@[simp] theorem advanceClassifiedResidualRoute_source_previous
    {FocusPrevious : Type uFocusPrevious}
    {focus : Core.Residual.Focus.Profile FocusPrevious}
    {schedule :
      _root_.Hypostructure.CT3.Schedule.FocusedContract.{uFocusPrevious + 1,
        uItem} focus}
    (contract :
      _root_.Hypostructure.CT3.ResidualRoute.Contract.{uFocusPrevious, uItem,
        uGood, uResidual, uInput, uOutcome, uTrace} schedule)
    (edge : Core.Routing.Edge) (previous : FocusPrevious) :
    (advanceClassifiedResidualRoute contract edge previous).previous.previous =
      previous :=
  contract.advanceClassified_source_previous edge previous

end Hypostructure.Graph.CT3
