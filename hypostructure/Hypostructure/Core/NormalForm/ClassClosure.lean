import Hypostructure.Core.ClosedLedger.Propagation
import Hypostructure.Core.Finite.Accounting

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
quotient.  Completeness of the finite family for the entire quotient is a
separate `TargetComplete` capability below. -/
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

/-- Every class of the current represented quotient is the null class. -/
def BoundaryZero {Previous : Type uPrevious}
    (profile : Profile.{uPrevious, uCarrier, uQuotient} Previous)
    (previous : Previous) : Prop :=
  forall quotientClass : (profile.quotientAt previous).Quotient,
    quotientClass = (profile.quotientAt previous).null

/-- The predecessor-owned finite family represents every nonnull quotient
class by a target-visible scheduled carrier.  This is the exact extra law
needed to upgrade an exhaustive finite visibility miss to vanishing of the
whole quotient. -/
structure TargetComplete {Previous : Type uPrevious}
    (profile : Profile.{uPrevious, uCarrier, uQuotient} Previous) : Prop where
  representsNonzero : forall (previous : Previous)
    (quotientClass : (profile.quotientAt previous).Quotient),
    Not (quotientClass = (profile.quotientAt previous).null) ->
      exists carrier : profile.Carrier,
        carrier ∈ (profile.familyAt previous).values /\
        (profile.quotientAt previous).project carrier = quotientClass /\
        profile.TargetVisible previous quotientClass

namespace TargetComplete

variable {Previous : Type uPrevious}
  {profile : Profile.{uPrevious, uCarrier, uQuotient} Previous}

/-- Target completeness identifies the finite executor's exhaustive miss with
literal vanishing of every class in the represented quotient. -/
theorem avoids_iff_boundaryZero (complete : TargetComplete profile)
    (previous : Previous) :
    profile.AvoidsTargetVisible previous <->
      BoundaryZero profile previous := by
  constructor
  · intro avoids quotientClass
    by_contra nonzero
    obtain ⟨carrier, member, projected, visible⟩ :=
      complete.representsNonzero previous quotientClass nonzero
    obtain ⟨index, equal⟩ :=
      (profile.familyAt previous).mem_iff_exists_index carrier |>.mp member
    have carrierVisible : profile.IsTargetVisible previous carrier := by
      unfold Profile.IsTargetVisible
      rw [projected]
      exact visible
    exact avoids index (by simpa [equal] using carrierVisible)
  · intro zero index visible
    exact profile.visibleNonzero previous visible
      (zero ((profile.quotientAt previous).project
        ((profile.familyAt previous).get index)))

/-- Named forward direction used by zero-quotient branch payloads. -/
theorem boundaryZero_of_avoids (complete : TargetComplete profile)
    {previous : Previous}
    (avoids : profile.AvoidsTargetVisible previous) :
    BoundaryZero profile previous :=
  (complete.avoids_iff_boundaryZero previous).mp avoids

/-- A literally zero quotient cannot contain a target-visible scheduled
class. -/
theorem avoids_of_boundaryZero (complete : TargetComplete profile)
    {previous : Previous} (zero : BoundaryZero profile previous) :
    profile.AvoidsTargetVisible previous :=
  (complete.avoids_iff_boundaryZero previous).mpr zero

end TargetComplete

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

/-- Audit nodes in one canonical class-closure generation. -/
inductive NodeId where
  | entry
  | firstVisibleScan
  | targetVisibleTerminal
  | zeroQuotientPropagation
  | zeroQuotientTerminal
  deriving DecidableEq, Repr

/-- Framework-generated branch payload indexed by its exact terminal. -/
inductive Outcome {Previous : Type uPrevious}
    (profile : Profile.{uPrevious, uCarrier, uQuotient} Previous)
    (registration : ExtensionRegistration.{uPrevious, uCarrier, uQuotient,
      uNextQuotient} profile)
    (previous : Previous) : Terminal -> Type _ where
  | targetVisible (visible : profile.HasTargetVisible previous)
      (residual : TargetVisibleResidual profile previous visible) :
      Outcome profile registration previous .targetVisible
  | zeroQuotient (avoids : profile.AvoidsTargetVisible previous)
      (propagation : ZeroQuotientPropagation profile registration previous
        avoids) :
      Outcome profile registration previous .zeroQuotient

/-- Terminal-indexed trace of the exact first-visible scan.  A hit retains its
literal schedule index; an exhaustive miss records the propagation pass. -/
inductive Trace {Previous : Type uPrevious}
    (profile : Profile.{uPrevious, uCarrier, uQuotient} Previous)
    (previous : Previous) : Terminal -> Type where
  | targetVisible (index : Fin (profile.familyAt previous).card) :
      Trace profile previous .targetVisible
  | zeroQuotient : Trace profile previous .zeroQuotient

namespace Trace

variable {Previous : Type uPrevious}
  {profile : Profile.{uPrevious, uCarrier, uQuotient} Previous}
  {previous : Previous}

/-- Observable node sequence selected by a generated terminal. -/
def nodes : {terminal : Terminal} -> Trace profile previous terminal ->
    List NodeId
  | .targetVisible, .targetVisible _ =>
      [.entry, .firstVisibleScan, .targetVisibleTerminal]
  | .zeroQuotient, .zeroQuotient =>
      [.entry, .firstVisibleScan, .zeroQuotientPropagation,
        .zeroQuotientTerminal]

/-- Exact primitive checks represented by a terminal-indexed scan trace. -/
def checks : {terminal : Terminal} -> Trace profile previous terminal -> Nat
  | .targetVisible, .targetVisible index => index.1 + 1
  | .zeroQuotient, .zeroQuotient => (profile.familyAt previous).card

/-- Canonical node sequence fixed by each semantic terminal. -/
def expectedNodes : Terminal -> List NodeId
  | .targetVisible => [.entry, .firstVisibleScan, .targetVisibleTerminal]
  | .zeroQuotient =>
      [.entry, .firstVisibleScan, .zeroQuotientPropagation,
        .zeroQuotientTerminal]

theorem nodes_eq_expected : {terminal : Terminal} ->
    (trace : Trace profile previous terminal) ->
      trace.nodes = expectedNodes terminal
  | .targetVisible, .targetVisible _ => rfl
  | .zeroQuotient, .zeroQuotient => rfl

end Trace

/-- The unique trace determined by one generated branch payload. -/
def traceOfOutcome {Previous : Type uPrevious}
    {profile : Profile.{uPrevious, uCarrier, uQuotient} Previous}
    {registration : ExtensionRegistration.{uPrevious, uCarrier, uQuotient,
      uNextQuotient} profile}
    {previous : Previous} {terminal : Terminal}
    (outcome : Outcome profile registration previous terminal) :
    Trace profile previous terminal :=
  match outcome with
  | .targetVisible _ residual => .targetVisible residual.hit.index
  | .zeroQuotient _ _ => .zeroQuotient

/-- Constructor-sealed, output-only result of class-closure generation.  It is
indexed by the literal predecessor but does not contain a predecessor stage,
so another framework executor can embed it in its own extension. -/
structure Generated {Previous : Type uPrevious}
    (profile : Profile.{uPrevious, uCarrier, uQuotient} Previous)
    (registration : ExtensionRegistration.{uPrevious, uCarrier, uQuotient,
      uNextQuotient} profile)
    (previous : Previous) where
  private mk ::
  terminal : Terminal
  outcome : Outcome profile registration previous terminal
  scan : Finite.Search.Execution (profile.familyAt previous)
    (profile.IsTargetVisible previous)
  scan_eq : scan = profile.scan previous
  trace_checks_exact : (traceOfOutcome outcome).checks =
    Finite.Accounting.executionChecks scan

/-- Terminal-refined view of a generated target-visible branch. -/
structure TargetVisibleOutput {Previous : Type uPrevious}
    (profile : Profile.{uPrevious, uCarrier, uQuotient} Previous)
    (previous : Previous) where
  private mk ::
  visible : profile.HasTargetVisible previous
  residual : TargetVisibleResidual profile previous visible

/-- Terminal-refined view of a generated zero-quotient branch. -/
structure ZeroQuotientOutput {Previous : Type uPrevious}
    (profile : Profile.{uPrevious, uCarrier, uQuotient} Previous)
    (registration : ExtensionRegistration.{uPrevious, uCarrier, uQuotient,
      uNextQuotient} profile)
    (previous : Previous) where
  private mk ::
  avoids : profile.AvoidsTargetVisible previous
  propagation : ZeroQuotientPropagation profile registration previous avoids

namespace ZeroQuotientOutput

/-- Under the separately registered target-completeness law, the generated
exhaustive miss proves that the entire represented quotient is literally
zero. -/
def boundaryZero {Previous : Type uPrevious}
    {profile : Profile.{uPrevious, uCarrier, uQuotient} Previous}
    {registration : ExtensionRegistration.{uPrevious, uCarrier, uQuotient,
      uNextQuotient} profile}
    {previous : Previous}
    (output : ZeroQuotientOutput profile registration previous)
    (complete : TargetComplete profile) : BoundaryZero profile previous :=
  complete.boundaryZero_of_avoids output.avoids

end ZeroQuotientOutput

namespace Generated

variable {Previous : Type uPrevious}
  {profile : Profile.{uPrevious, uCarrier, uQuotient} Previous}
  {registration : ExtensionRegistration.{uPrevious, uCarrier, uQuotient,
    uNextQuotient} profile}
  {previous : Previous}

/-- Exact terminal-indexed trace retained by a generated output. -/
def trace (generated : Generated profile registration previous) :
    Trace profile previous generated.terminal :=
  traceOfOutcome generated.outcome

/-- Observable exact trace nodes. -/
def traceNodes (generated : Generated profile registration previous) :
    List NodeId :=
  generated.trace.nodes

/-- Exact primitive checks represented by the generated trace. -/
def checks (generated : Generated profile registration previous) : Nat :=
  generated.trace.checks

theorem traceNodes_eq_expected
    (generated : Generated profile registration previous) :
    generated.traceNodes = Trace.expectedNodes generated.terminal :=
  Trace.nodes_eq_expected generated.trace

/-- Generated checks are exactly those of the canonical first-visible scan. -/
theorem checks_eq_canonical_scan
    (generated : Generated profile registration previous) :
    generated.checks =
      Finite.Accounting.executionChecks (profile.scan previous) := by
  rw [checks, trace, generated.trace_checks_exact, generated.scan_eq]

/-- Exact scan work is bounded by the cardinality of the family queried from
the literal predecessor. -/
theorem checks_le_family_card
    (generated : Generated profile registration previous) :
    generated.checks <= (profile.familyAt previous).card := by
  rw [generated.checks_eq_canonical_scan]
  exact Finite.Accounting.executionChecks_le_card (profile.scan previous)

/-- Degree-one work budget over the exact family queried from the predecessor. -/
def workBudget (profile : Profile.{uPrevious, uCarrier, uQuotient} Previous)
    (registration : ExtensionRegistration.{uPrevious, uCarrier, uQuotient,
      uNextQuotient} profile)
    (previous : Previous) :
    PolynomialCheckBudget (Generated profile registration previous) where
  size := fun _generated => (profile.familyAt previous).card
  checks := checks
  coefficient := 1
  degree := 1
  bounded := by
    intro generated
    exact generated.checks_le_family_card.trans (by simp)

@[simp] theorem workBudget_size
    (generated : Generated profile registration previous) :
    (workBudget profile registration previous).size generated =
      (profile.familyAt previous).card :=
  rfl

@[simp] theorem workBudget_checks
    (generated : Generated profile registration previous) :
    (workBudget profile registration previous).checks generated =
      generated.checks :=
  rfl

/-- Recover the exact target-visible residual only from that terminal. -/
def targetVisibleResidual
    (generated : Generated profile registration previous)
    (isTargetVisible : generated.terminal = .targetVisible) :
    TargetVisibleOutput profile previous := by
  rcases generated with
    ⟨terminal, outcome, scan, scan_eq, trace_checks_exact⟩
  cases outcome with
  | targetVisible visible residual => exact ⟨visible, residual⟩
  | zeroQuotient _ _ => cases isTargetVisible

/-- Recover the exact zero-quotient propagation only from that terminal. -/
def zeroQuotientPropagation
    (generated : Generated profile registration previous)
    (isZeroQuotient : generated.terminal = .zeroQuotient) :
    ZeroQuotientOutput profile registration previous := by
  rcases generated with
    ⟨terminal, outcome, scan, scan_eq, trace_checks_exact⟩
  cases outcome with
  | targetVisible _ _ => cases isZeroQuotient
  | zeroQuotient avoids propagation => exact ⟨avoids, propagation⟩

end Generated

/-- Exact predecessor-indexed work budget for embedding class closure inside
another focused or routed framework executor. -/
def generationBudget {Previous : Type uPrevious}
    (profile : Profile.{uPrevious, uCarrier, uQuotient} Previous) :
    PolynomialCheckBudget Previous where
  size := fun previous => (profile.familyAt previous).card
  checks := fun previous =>
    Finite.Accounting.executionChecks (profile.scan previous)
  coefficient := 1
  degree := 1
  bounded := by
    intro previous
    exact (Finite.Accounting.executionChecks_le_card
      (profile.scan previous)).trans (by simp)

/-- Generate one exact semantic branch without wrapping the predecessor in a
decision or continuation stage.  The count is the canonical scan's visible
primitive inspections. -/
def generateCounted {Previous : Type uPrevious}
    (profile : Profile.{uPrevious, uCarrier, uQuotient} Previous)
    (registration : ExtensionRegistration.{uPrevious, uCarrier, uQuotient,
      uNextQuotient} profile)
    (previous : Previous) : Counted (Generated profile registration previous) :=
  let scan := profile.scan previous
  let generated : Generated profile registration previous :=
    match found : scan.hit? with
    | some hit =>
        let visible : profile.HasTargetVisible previous :=
          scan.hasHit_of_eq_some found
        let residual : TargetVisibleResidual profile previous visible := {
          hit := hit
          targetVisible := hit.sound
          quotientNonzero := profile.visibleNonzero previous hit.sound
        }
        {
          terminal := .targetVisible
          outcome := .targetVisible visible residual
          scan := scan
          scan_eq := rfl
          trace_checks_exact := by
            exact (Finite.Accounting.executionChecks_of_hit scan hit found).symm
        }
    | none =>
        let avoids : profile.AvoidsTargetVisible previous :=
          scan.exhaustive found
        let propagation := zeroPropagation profile registration previous avoids
        {
          terminal := .zeroQuotient
          outcome := .zeroQuotient avoids propagation
          scan := scan
          scan_eq := rfl
          trace_checks_exact := by
            exact (Finite.Accounting.executionChecks_of_miss scan found).symm
        }
  ⟨generated, generated.checks⟩

@[simp] theorem generateCounted_checks {Previous : Type uPrevious}
    (profile : Profile.{uPrevious, uCarrier, uQuotient} Previous)
    (registration : ExtensionRegistration.{uPrevious, uCarrier, uQuotient,
      uNextQuotient} profile)
    (previous : Previous) :
    (generateCounted profile registration previous).checks =
      Finite.Accounting.executionChecks (profile.scan previous) :=
  (generateCounted profile registration previous).value.checks_eq_canonical_scan

@[simp] theorem generateCounted_checks_eq_budget {Previous : Type uPrevious}
    (profile : Profile.{uPrevious, uCarrier, uQuotient} Previous)
    (registration : ExtensionRegistration.{uPrevious, uCarrier, uQuotient,
      uNextQuotient} profile)
    (previous : Previous) :
    (generateCounted profile registration previous).checks =
      (generationBudget profile).checks previous :=
  generateCounted_checks profile registration previous

/-- Generated work never exceeds the exact predecessor-owned family. -/
theorem generateCounted_checks_le_family_card {Previous : Type uPrevious}
    (profile : Profile.{uPrevious, uCarrier, uQuotient} Previous)
    (registration : ExtensionRegistration.{uPrevious, uCarrier, uQuotient,
      uNextQuotient} profile)
    (previous : Previous) :
    (generateCounted profile registration previous).checks <=
      (profile.familyAt previous).card := by
  rw [generateCounted_checks]
  exact Finite.Accounting.executionChecks_le_card (profile.scan previous)

/-- The counted generator satisfies its registered degree-one work envelope. -/
theorem generateCounted_checks_le_polynomial {Previous : Type uPrevious}
    (profile : Profile.{uPrevious, uCarrier, uQuotient} Previous)
    (registration : ExtensionRegistration.{uPrevious, uCarrier, uQuotient,
      uNextQuotient} profile)
    (previous : Previous) :
    (generateCounted profile registration previous).checks <=
      (Generated.workBudget profile registration previous).coefficient *
        ((Generated.workBudget profile registration previous).size
          (generateCounted profile registration previous).value + 1) ^
        (Generated.workBudget profile registration previous).degree := by
  change (generateCounted profile registration previous).value.checks <= _
  exact (Generated.workBudget profile registration previous).bounded
    (generateCounted profile registration previous).value

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

namespace Generated

/-- Binary decision payload determined by one generated semantic outcome. -/
private def binaryOfOutcome {Previous : Type uPrevious}
    {profile : Profile.{uPrevious, uCarrier, uQuotient} Previous}
    {registration : ExtensionRegistration.{uPrevious, uCarrier, uQuotient,
      uNextQuotient} profile}
    {previous : Previous} {terminal : Terminal}
    (outcome : Outcome profile registration previous terminal) :
    Residual.Decision.Binary profile.HasTargetVisible
      profile.AvoidsTargetVisible previous :=
  match outcome with
  | .targetVisible visible _ => .yesBranch visible
  | .zeroQuotient avoids _ => .noBranch avoids

/-- Dependent continuation payload determined by the same generated outcome. -/
private def continuationOfOutcome {Previous : Type uPrevious}
    {profile : Profile.{uPrevious, uCarrier, uQuotient} Previous}
    {registration : ExtensionRegistration.{uPrevious, uCarrier, uQuotient,
      uNextQuotient} profile}
    {previous : Previous} {terminal : Terminal}
    (outcome : Outcome profile registration previous terminal) :
    Residual.Decision.Continuation
      (fun previous visible => TargetVisibleResidual profile previous visible)
      (fun previous avoids =>
        ZeroQuotientPropagation profile registration previous avoids)
      previous (binaryOfOutcome outcome) :=
  match outcome with
  | .targetVisible visible residual => .yesBranch visible residual
  | .zeroQuotient avoids propagation => .noBranch avoids propagation

/-- Decision stage reconstructed from a generated output.  Its predecessor is
definitionally the literal incoming stage; only its added value inspects the
generated branch. -/
private def decisionOfGenerated {Previous : Type uPrevious}
    {profile : Profile.{uPrevious, uCarrier, uQuotient} Previous}
    {registration : ExtensionRegistration.{uPrevious, uCarrier, uQuotient,
      uNextQuotient} profile}
    {previous : Previous} (generated : Generated profile registration previous) :
    Residual.Decision.Stage profile.HasTargetVisible
      profile.AvoidsTargetVisible :=
  Residual.Ledger.extend previous (binaryOfOutcome generated.outcome)

/-- Compatibility assembly for consumers that still require the historical
two-stage decision/continuation shape. -/
def toStage {Previous : Type uPrevious}
    {profile : Profile.{uPrevious, uCarrier, uQuotient} Previous}
    {registration : ExtensionRegistration.{uPrevious, uCarrier, uQuotient,
      uNextQuotient} profile}
    {previous : Previous} (generated : Generated profile registration previous) :
    Stage profile registration :=
  Residual.Ledger.extend (decisionOfGenerated generated)
    (continuationOfOutcome generated.outcome)

@[simp] theorem toStage_previous {Previous : Type uPrevious}
    {profile : Profile.{uPrevious, uCarrier, uQuotient} Previous}
    {registration : ExtensionRegistration.{uPrevious, uCarrier, uQuotient,
      uNextQuotient} profile}
    {previous : Previous} (generated : Generated profile registration previous) :
    generated.toStage.previous.previous = previous := by
  rfl

end Generated

/-- Execute the canonical visibility decision and both typed continuations. -/
def run {Previous : Type uPrevious}
    (profile : Profile.{uPrevious, uCarrier, uQuotient} Previous)
    (registration : ExtensionRegistration.{uPrevious, uCarrier, uQuotient,
      uNextQuotient} profile) (previous : Previous) :
    Stage profile registration :=
  (generateCounted profile registration previous).value.toStage

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

theorem terminal_toStage {Previous : Type uPrevious}
    {profile : Profile.{uPrevious, uCarrier, uQuotient} Previous}
    {registration : ExtensionRegistration.{uPrevious, uCarrier, uQuotient,
      uNextQuotient} profile}
    {previous : Previous} (generated : Generated profile registration previous) :
    terminal generated.toStage = generated.terminal := by
  rcases generated with
    ⟨generatedTerminal, outcome, scan, scan_eq, trace_checks_exact⟩
  cases outcome <;> rfl

theorem run_terminal_eq_generated {Previous : Type uPrevious}
    (profile : Profile.{uPrevious, uCarrier, uQuotient} Previous)
    (registration : ExtensionRegistration.{uPrevious, uCarrier, uQuotient,
      uNextQuotient} profile) (previous : Previous) :
    terminal (run profile registration previous) =
      (generateCounted profile registration previous).value.terminal :=
  terminal_toStage (generateCounted profile registration previous).value

end Hypostructure.Core.NormalForm.ClassClosure
