import Hypostructure.Core.ClosedLedger.Propagation
import Hypostructure.Core.Finite.Search

/-!
# Class-closure normal form

This executor scans the exact represented remainder family against the
registered target projection.  A first visible quotient class is retained as
an exact residual.  An exhaustive miss proves every represented class
target-null, extends the closed-class ledger, and installs the registered
quotient propagation.  Applications neither select the branch nor construct
the successor ledger.
-/

namespace Hypostructure.Core.NormalForm.ClassClosure

open Hypostructure.Core

universe uPrevious uCarrier uQuotient uNextQuotient

/-- Domain-independent data for a represented class family and its current
target-complete quotient. -/
structure Profile (Previous : Type uPrevious) where
  Carrier : Type uCarrier
  closure : ClosureOperator Carrier
  TargetNull : Carrier -> Prop
  family : Residual.Query Previous fun _previous =>
    Finite.Enumeration Carrier
  ledger : Residual.Query Previous fun _previous =>
    ClosedClassLedger closure TargetNull
  quotient : (previous : Previous) ->
    LedgerQuotient.{uCarrier, uQuotient} (ledger.read previous)
  TargetVisible : (previous : Previous) ->
    (quotient previous).Quotient -> Prop
  targetVisibleDecidable : (previous : Previous) ->
    (quotientClass : (quotient previous).Quotient) ->
      Decidable (TargetVisible previous quotientClass)
  visibleNonzero : forall (previous : Previous) {carrier : Carrier},
    TargetVisible previous ((quotient previous).project carrier) ->
      Not ((quotient previous).project carrier = (quotient previous).null)
  nullOfNotVisible : forall (previous : Previous) (carrier : Carrier),
    Not (TargetVisible previous ((quotient previous).project carrier)) ->
      (quotient previous).project carrier = (quotient previous).null
  targetNullOfNull : forall (previous : Previous) (carrier : Carrier),
    (quotient previous).project carrier = (quotient previous).null ->
      TargetNull carrier
  closureStable : ClosureStable closure TargetNull

namespace Profile

variable {Previous : Type uPrevious}
  (profile : Profile.{uPrevious, uCarrier, uQuotient} Previous)

/-- The exact remainder enumeration queried from the predecessor ledger. -/
abbrev familyAt (previous : Previous) : Finite.Enumeration profile.Carrier :=
  profile.family.read previous

/-- The exact accumulated closed-class ledger queried from the predecessor. -/
abbrev ledgerAt (previous : Previous) :
    ClosedClassLedger profile.closure profile.TargetNull :=
  profile.ledger.read previous

/-- The registered target projection at the literal predecessor. -/
abbrev quotientAt (previous : Previous) :
    LedgerQuotient.{uCarrier, uQuotient} (profile.ledgerAt previous) :=
  profile.quotient previous

/-- Target visibility of one represented carrier class. -/
def IsTargetVisible (previous : Previous) (carrier : profile.Carrier) : Prop :=
  profile.TargetVisible previous
    ((profile.quotientAt previous).project carrier)

/-- The represented family as a set of generators for ledger extension. -/
def familySet (previous : Previous) : Set profile.Carrier :=
  {carrier | carrier ∈ (profile.familyAt previous).values}

/-- Canonical first-visible-class scan on the exact predecessor-owned family. -/
def scan (previous : Previous) :
    Finite.Search.Execution (profile.familyAt previous)
      (profile.IsTargetVisible previous) :=
  Finite.Search.run (profile.familyAt previous)
    (profile.IsTargetVisible previous)
    (fun carrier =>
      profile.targetVisibleDecidable previous
        ((profile.quotientAt previous).project carrier))

/-- Executable proposition selecting the target-visible branch. -/
def HasTargetVisible (previous : Previous) : Prop :=
  (profile.scan previous).HasHit

/-- Exact exhaustive complement of target visibility on the represented
family. -/
def AvoidsTargetVisible (previous : Previous) : Prop :=
  Finite.Search.Avoids (profile.familyAt previous)
    (profile.IsTargetVisible previous)

/-- Core decision node derived from the canonical scan. -/
def decisionNode : Residual.Decision.Node Previous
    profile.HasTargetVisible profile.AvoidsTargetVisible :=
  Residual.Decision.Node.create
    (fun previous =>
      Finite.Search.Execution.instDecidableHasHit (profile.scan previous))
    (fun previous absent =>
      (profile.scan previous).avoids_of_not_hasHit absent)

/-- Every member of an exhaustively invisible represented family is
target-null by target completeness of the registered quotient. -/
theorem targetNull_of_avoids (previous : Previous)
    (avoids : profile.AvoidsTargetVisible previous) {carrier : profile.Carrier}
    (member : carrier ∈ (profile.familyAt previous).values) :
    profile.TargetNull carrier := by
  obtain ⟨index, equal⟩ :=
    (profile.familyAt previous).mem_iff_exists_index carrier |>.mp member
  have invisible : Not (profile.IsTargetVisible previous carrier) := by
    intro visible
    exact avoids index (by simpa [equal] using visible)
  exact profile.targetNullOfNull previous carrier
    (profile.nullOfNotVisible previous carrier invisible)

/-- The exact enlarged ledger produced by the zero-quotient branch. -/
def extendedLedger (previous : Previous)
    (avoids : profile.AvoidsTargetVisible previous) :
    ClosedClassLedger profile.closure profile.TargetNull :=
  (profile.ledgerAt previous).extend profile.closureStable
    (profile.familySet previous)
    (fun member => profile.targetNull_of_avoids previous avoids member)

end Profile

/-- Domain registration for the quotient induced by the exact enlarged
ledger.  Core constructs the propagation; the domain supplies only the
quotient universal property and its induced quotient map. -/
structure ExtensionRegistration {Previous : Type uPrevious}
    (profile : Profile.{uPrevious, uCarrier, uQuotient} Previous) where
  nextQuotient : (previous : Previous) ->
    (avoids : profile.AvoidsTargetVisible previous) ->
      LedgerQuotient.{uCarrier, uNextQuotient}
        (profile.extendedLedger previous avoids)
  quotientTransport : (previous : Previous) ->
    (avoids : profile.AvoidsTargetVisible previous) ->
      (profile.quotientAt previous).Quotient ->
        (nextQuotient previous avoids).Quotient
  quotientTransport_project : forall (previous : Previous)
    (avoids : profile.AvoidsTargetVisible previous) (carrier : profile.Carrier),
    quotientTransport previous avoids
        ((profile.quotientAt previous).project carrier) =
      (nextQuotient previous avoids).project carrier
  quotientTransport_null : forall (previous : Previous)
    (avoids : profile.AvoidsTargetVisible previous),
    quotientTransport previous avoids (profile.quotientAt previous).null =
      (nextQuotient previous avoids).null

/-- The exact target-visible class residual selected by the canonical scan. -/
structure TargetVisibleResidual {Previous : Type uPrevious}
    (profile : Profile.{uPrevious, uCarrier, uQuotient} Previous)
    (previous : Previous) (visible : profile.HasTargetVisible previous) where
  private mk ::
  hit : Finite.Search.IndexedHit (profile.familyAt previous)
    (profile.IsTargetVisible previous)
  targetVisible : profile.IsTargetVisible previous hit.value
  quotientNonzero :
    Not ((profile.quotientAt previous).project hit.value =
      (profile.quotientAt previous).null)

/-- Framework-owned zero-quotient successor.  It carries the existing Core
propagation and records inclusion of the exact represented family. -/
structure ZeroQuotientPropagation {Previous : Type uPrevious}
    (profile : Profile.{uPrevious, uCarrier, uQuotient} Previous)
    (registration : ExtensionRegistration.{uPrevious, uCarrier, uQuotient,
      uNextQuotient} profile)
    (previous : Previous) (avoids : profile.AvoidsTargetVisible previous) where
  private mk ::
  nextQuotient : LedgerQuotient.{uCarrier, uNextQuotient}
    (profile.extendedLedger previous avoids)
  propagation : LedgerPropagation.{uCarrier, uQuotient, uCarrier,
    uNextQuotient} (profile.ledgerAt previous) (profile.quotientAt previous)
  representedFamilyIncluded : forall {carrier : profile.Carrier},
    carrier ∈ (profile.familyAt previous).values ->
      carrier ∈ (profile.extendedLedger previous avoids).classes

namespace ZeroQuotientPropagation

variable {Previous : Type uPrevious}
  {profile : Profile.{uPrevious, uCarrier, uQuotient} Previous}
  {registration : ExtensionRegistration.{uPrevious, uCarrier, uQuotient,
    uNextQuotient} profile}
  {previous : Previous} {avoids : profile.AvoidsTargetVisible previous}

/-- Previously closed classes remain killed after a normal-form propagation. -/
theorem priorClassRemainsKilled
    (result : ZeroQuotientPropagation profile registration previous avoids)
    {carrier : profile.Carrier}
    (closed : carrier ∈ (profile.ledgerAt previous).classes) :
    result.propagation.nextQuotient.project
        (result.propagation.transport carrier) =
      result.propagation.nextQuotient.null :=
  result.propagation.priorClosedClassesRemainKilled closed

end ZeroQuotientPropagation

/-- Build the exact same-carrier ledger propagation selected by an exhaustive
visibility miss. -/
def zeroPropagation {Previous : Type uPrevious}
    (profile : Profile.{uPrevious, uCarrier, uQuotient} Previous)
    (registration : ExtensionRegistration.{uPrevious, uCarrier, uQuotient,
      uNextQuotient} profile)
    (previous : Previous) (avoids : profile.AvoidsTargetVisible previous) :
    ZeroQuotientPropagation profile registration previous avoids := by
  let propagation : LedgerPropagation.{uCarrier, uQuotient, uCarrier,
      uNextQuotient} (profile.ledgerAt previous)
      (profile.quotientAt previous) := {
    NextCarrier := profile.Carrier
    nextClosure := profile.closure
    nextTargetNull := profile.TargetNull
    transport := id
    nextLedger := profile.extendedLedger previous avoids
    nextQuotient := registration.nextQuotient previous avoids
    includesTransport := by
      intro carrier closed
      exact (profile.ledgerAt previous).subset_extend profile.closureStable
        (profile.familySet previous)
        (fun member => profile.targetNull_of_avoids previous avoids member)
        closed
    quotientTransport := registration.quotientTransport previous avoids
    quotientTransport_project :=
      registration.quotientTransport_project previous avoids
    quotientTransport_null :=
      registration.quotientTransport_null previous avoids
  }
  refine {
    nextQuotient := registration.nextQuotient previous avoids
    propagation := propagation
    representedFamilyIncluded := ?_
  }
  intro carrier member
  exact (profile.ledgerAt previous).added_subset_extend profile.closureStable
    (profile.familySet previous)
    (fun familyMember =>
      profile.targetNull_of_avoids previous avoids familyMember)
    member

/-- Recover the exact first visible class and its nonzero quotient proof. -/
def targetVisibleResidual {Previous : Type uPrevious}
    (profile : Profile.{uPrevious, uCarrier, uQuotient} Previous)
    (previous : Previous) (visible : profile.HasTargetVisible previous) :
    TargetVisibleResidual profile previous visible := by
  let hit := (profile.scan previous).hitOfHasHit visible
  exact {
    hit := hit
    targetVisible := hit.sound
    quotientNonzero := profile.visibleNonzero previous hit.sound
  }

/-- The two semantic normal-form terminals. -/
inductive Terminal where
  | zeroQuotient
  | targetVisible
  deriving DecidableEq, Repr

/-- Framework-owned dependent successor stage.  Its predecessor is the Core
decision stage, whose predecessor is the literal incoming ledger. -/
abbrev Stage {Previous : Type uPrevious}
    (profile : Profile.{uPrevious, uCarrier, uQuotient} Previous)
    (registration : ExtensionRegistration.{uPrevious, uCarrier, uQuotient,
      uNextQuotient} profile) :=
  Residual.Decision.ContinuationStage
    (Previous := Previous)
    (Yes := profile.HasTargetVisible)
    (No := profile.AvoidsTargetVisible)
    (fun previous visible => TargetVisibleResidual profile previous visible)
    (fun previous avoids =>
      ZeroQuotientPropagation profile registration previous avoids)

/-- Execute the canonical visibility decision and both typed continuations. -/
def run {Previous : Type uPrevious}
    (profile : Profile.{uPrevious, uCarrier, uQuotient} Previous)
    (registration : ExtensionRegistration.{uPrevious, uCarrier, uQuotient,
      uNextQuotient} profile) (previous : Previous) :
    Stage profile registration :=
  let decision := profile.decisionNode.run previous
  Residual.Decision.advance decision
    (fun visible => targetVisibleResidual profile decision.previous visible)
    (fun avoids =>
      zeroPropagation profile registration decision.previous avoids)

@[simp] theorem run_previous {Previous : Type uPrevious}
    (profile : Profile.{uPrevious, uCarrier, uQuotient} Previous)
    (registration : ExtensionRegistration.{uPrevious, uCarrier, uQuotient,
      uNextQuotient} profile) (previous : Previous) :
    (run profile registration previous).previous.previous = previous :=
  rfl

/-- Observable terminal, derived only from the Core decision constructor. -/
def terminal {Previous : Type uPrevious}
    {profile : Profile.{uPrevious, uCarrier, uQuotient} Previous}
    {registration : ExtensionRegistration.{uPrevious, uCarrier, uQuotient,
      uNextQuotient} profile} (stage : Stage profile registration) : Terminal :=
  match stage.previous.added with
  | .yesBranch _ => .targetVisible
  | .noBranch _ => .zeroQuotient

end Hypostructure.Core.NormalForm.ClassClosure
