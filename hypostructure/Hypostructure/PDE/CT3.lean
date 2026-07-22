import Hypostructure.CT3.Automation
import Hypostructure.CT3.ResidualRoute
import Hypostructure.CT3.RunSchedule
import Hypostructure.CT3.SameInterface
import Hypostructure.PDE.Model

/-!
# PDE specialization of CT3

The PDE adapter interprets CT3 representatives as local terms and coordinates
as exact local-tail contexts.  It introduces no PDE-specific search or routing:
CT3 owns compression, distinguishing coordinates, table lookup, residuals, and
work accounting.
-/

namespace Hypostructure.PDE.CT3

universe uPrevious u uContext uCoordinate uCandidate uRow
universe uFocusPrevious uItem uGood uResidual uInput uOutcome uTrace

/-- Exact Boolean response system for additive local/tail assembly. -/
noncomputable abbrev targetSystem
    (M : LocalModel.{u}) [Add M.problem.Ambient]
    (Target : M.problem.Ambient -> Prop)
    (decideTarget : forall object, Decidable (Target object))
    (Context : Type uContext)
    (tail : Context -> M.problem.Ambient)
    (Coordinate : Type uCoordinate)
    (decode : Coordinate -> Context) :
    Core.Response.System M.problem.Ambient :=
  Core.Response.System.ofDecodedContexts Context Coordinate Bool
    (fun atom context =>
      @decide (Target (atom + tail context))
        (decideTarget (atom + tail context)))
    decode

/-- Exact target semantics for the additive Boolean response system. -/
noncomputable def targetSemantics
    (M : LocalModel.{u}) [Add M.problem.Ambient]
    (Target : M.problem.Ambient -> Prop)
    (decideTarget : forall object, Decidable (Target object))
    (Context : Type uContext)
    (tail : Context -> M.problem.Ambient)
    (Coordinate : Type uCoordinate)
    (decode : Coordinate -> Context) :
    Core.Response.TargetSemantics
      (targetSystem M Target decideTarget Context tail Coordinate decode) where
  TargetResponse := fun atom context => Target (atom + tail context)
  Accepts := fun response => response = true
  target_iff_accepts := by
    intro atom context
    change Target (atom + tail context) ↔
      @decide (Target (atom + tail context))
        (decideTarget (atom + tail context)) = true
    exact decide_eq_true_iff.symm

/-- CT3 target-response specification for PDE local representatives. -/
noncomputable abbrev targetSpec
    (Previous : Type uPrevious)
    (M : LocalModel.{u}) [Add M.problem.Ambient]
    (Target : M.problem.Ambient -> Prop)
    (decideTarget : forall object, Decidable (Target object))
    (Context : Type uContext)
    (tail : Context -> M.problem.Ambient)
    (Coordinate : Type uCoordinate)
    (decode : Coordinate -> Context)
    (Candidate : Type uCandidate)
    (candidatePiece : Candidate -> M.problem.Ambient)
    (Row : Type uRow)
    (rowPiece : Row -> M.problem.Ambient)
    (rowResponse : Row ->
      (targetSystem M Target decideTarget Context tail Coordinate decode).Coordinate ->
        (targetSystem M Target decideTarget Context tail Coordinate decode).Value)
    (Admissible : Previous -> M.problem.Ambient -> Candidate -> Prop)
    (StrictlySmaller : Previous -> M.problem.Ambient -> Candidate -> Prop) :
    _root_.Hypostructure.CT3.Spec Previous where
  Representative := M.problem.Ambient
  Candidate := Candidate
  Row := Row
  system := targetSystem M Target decideTarget Context tail Coordinate decode
  semantics := targetSemantics M Target decideTarget Context tail Coordinate
    decode
  candidatePiece := candidatePiece
  rowPiece := rowPiece
  rowResponse := rowResponse
  Admissible := Admissible
  StrictlySmaller := StrictlySmaller

section TerminalSemantics

variable {Previous : Type uPrevious}
  {M : LocalModel.{u}} [Add M.problem.Ambient]
  {Target : M.problem.Ambient -> Prop}
  {decideTarget : forall object, Decidable (Target object)}
  {Context : Type uContext}
  {tail : Context -> M.problem.Ambient}
  {Coordinate : Type uCoordinate}
  {decode : Coordinate -> Context}
  {Candidate : Type uCandidate}
  {candidatePiece : Candidate -> M.problem.Ambient}
  {Row : Type uRow}
  {rowPiece : Row -> M.problem.Ambient}
  {rowResponse : Row ->
    (targetSystem M Target decideTarget Context tail Coordinate decode).Coordinate ->
      (targetSystem M Target decideTarget Context tail Coordinate decode).Value}
  {Admissible : Previous -> M.problem.Ambient -> Candidate -> Prop}
  {StrictlySmaller : Previous -> M.problem.Ambient -> Candidate -> Prop}

local notation "pdeSpec" =>
  targetSpec Previous M Target decideTarget Context tail Coordinate decode
    Candidate candidatePiece Row rowPiece rowResponse Admissible
    StrictlySmaller

/-- A CT3 compression certificate transports the PDE target through every
registered additive tail context. -/
theorem compression_target_iff
    {capability : _root_.Hypostructure.CT3.Capability pdeSpec}
    {previous : Previous}
    (certificate : _root_.Hypostructure.CT3.CompressionCertificate capability
      previous)
    (context : Context) :
    Target ((capability.sourceAt previous) + tail context) ↔
      Target ((candidatePiece certificate.candidate) + tail context) :=
  certificate.target_iff context

end TerminalSemantics

/-! ## Scheduled bounded-entry execution -/

/-- PDE adapter for the CT3-owned scheduled executor.  PDE supplies no
table plumbing or route selection here: the caller provides the registered PDE
CT3 spec/capability and the residual-owned item-to-input query, and CT3 derives
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

/-- Retrieve the exact per-item PDE CT3 result through the same active
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

/-- Execute PDE scheduled CT3 and terminal classification in one
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

/-- PDE adapter for CT3-owned all-good same-interface registration after
schedule classification.  PDE supplies no package routing; the package
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

/-- PDE adapter for CT3-owned first-residual routing after schedule
classification.  PDE supplies no routing logic; the route contract is the
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

end Hypostructure.PDE.CT3
