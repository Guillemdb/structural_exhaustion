import Hypostructure.Core.NormalForm.ClassClosure

/-!
# Counted output-only class-closure fixture

Two exact predecessor-owned families exercise first-visible and exhaustive-miss
generation.  The generated output is also embedded directly in another ledger
extension, without retaining an intermediate class-closure predecessor stage.
-/

namespace Hypostructure.Fixtures.ClassClosureCounted

open Hypostructure.Core
open Core.NormalForm

inductive Carrier where
  | closed
  | pending
  | live
  deriving DecidableEq, Repr

def project : Carrier -> Bool
  | .closed | .pending => false
  | .live => true

def targetNull (carrier : Carrier) : Prop :=
  project carrier = false

def closure : ClosureOperator Carrier :=
  ClosureOperator.identity Carrier

def closureStable : ClosureStable closure targetNull :=
  ClosureStable.identity

def initialLedger : ClosedClassLedger closure targetNull where
  classes := {carrier | carrier = .closed}
  closed := rfl
  targetNull := by
    intro carrier equal
    subst carrier
    rfl

def quotientUniversal : QuotientUniversalProperty project where
  descend := fun map _compatible quotientClass =>
    match quotientClass with
    | false => map .closed
    | true => map .live
  descend_project := by
    intro Result map compatible carrier
    cases carrier with
    | closed => rfl
    | pending =>
        exact compatible (x := Carrier.closed) (y := Carrier.pending) rfl
    | live => rfl
  descend_unique := by
    intro Result map compatible candidate commutes quotientClass
    cases quotientClass with
    | false => exact commutes .closed
    | true => exact commutes .live

def initialQuotient : LedgerQuotient initialLedger where
  Quotient := Bool
  project := project
  null := false
  killsClosed := by
    intro carrier equal
    subst carrier
    rfl
  universal := quotientUniversal

structure Residual where
  family : Finite.Enumeration Carrier

abbrev Previous := Residual.Ledger Residual

def residualQuery : Residual.Query Previous fun _previous => Residual :=
  Residual.Query.residual

def familyQuery : Residual.Query Previous fun _previous =>
    Finite.Enumeration Carrier :=
  residualQuery.map fun _previous residual => residual.family

def ledgerQuery : Residual.Query Previous fun _previous =>
    ClosedClassLedger closure targetNull :=
  residualQuery.map fun _previous _residual => initialLedger

def profile : ClassClosure.Profile Previous where
  Carrier := Carrier
  closure := closure
  TargetNull := targetNull
  family := familyQuery
  ledger := ledgerQuery
  quotient := fun _previous => initialQuotient
  TargetVisible := fun _previous quotientClass => quotientClass = true
  targetVisibleDecidable := fun _previous quotientClass =>
    Bool.decEq quotientClass true
  visibleNonzero := by
    intro previous carrier visible equalNull
    change project carrier = true at visible
    change project carrier = false at equalNull
    simp_all
  nullOfNotVisible := by
    intro previous carrier invisible
    change Not (project carrier = true) at invisible
    cases equal : project carrier with
    | false => exact equal
    | true => exact (invisible equal).elim
  targetNullOfNull := by
    intro previous carrier equalNull
    exact equalNull
  closureStable := closureStable

def nextQuotient (previous : Previous)
    (avoids : profile.AvoidsTargetVisible previous) :
    LedgerQuotient (profile.extendedLedger previous avoids) where
  Quotient := Bool
  project := project
  null := false
  killsClosed := by
    intro carrier closed
    exact (profile.extendedLedger previous avoids).targetNull closed
  universal := quotientUniversal

def registration : ClassClosure.ExtensionRegistration profile where
  nextQuotient := nextQuotient
  quotientTransport := fun _previous _avoids => id
  quotientTransport_project := by intros; rfl
  quotientTransport_null := by intros; rfl

def visibleFamily : Finite.Enumeration Carrier where
  values := [.pending, .live, .closed]
  nodup := by simp
  decEq := inferInstance

def zeroFamily : Finite.Enumeration Carrier where
  values := [.pending, .closed]
  nodup := by simp
  decEq := inferInstance

def visiblePrevious : Previous :=
  Residual.Ledger.initial ⟨visibleFamily⟩

def zeroPrevious : Previous :=
  Residual.Ledger.initial ⟨zeroFamily⟩

def visibleGeneration :=
  ClassClosure.generateCounted profile registration visiblePrevious

def zeroGeneration :=
  ClassClosure.generateCounted profile registration zeroPrevious

theorem visible_terminal :
    visibleGeneration.value.terminal = .targetVisible := by
  decide

theorem zero_terminal :
    zeroGeneration.value.terminal = .zeroQuotient := by
  decide

theorem visible_trace_exact :
    visibleGeneration.value.traceNodes =
      [.entry, .firstVisibleScan, .targetVisibleTerminal] := by
  rw [ClassClosure.Generated.traceNodes_eq_expected, visible_terminal]
  rfl

theorem zero_trace_exact :
    zeroGeneration.value.traceNodes =
      [.entry, .firstVisibleScan, .zeroQuotientPropagation,
        .zeroQuotientTerminal] := by
  rw [ClassClosure.Generated.traceNodes_eq_expected, zero_terminal]
  rfl

theorem visible_checks_exact : visibleGeneration.checks = 2 := by
  decide

theorem zero_checks_exact : zeroGeneration.checks = 2 := by
  decide

theorem visible_work_uses_exact_family :
    visibleGeneration.checks <= (profile.familyAt visiblePrevious).card :=
  ClassClosure.generateCounted_checks_le_family_card
    profile registration visiblePrevious

theorem zero_work_uses_exact_family :
    zeroGeneration.checks <= (profile.familyAt zeroPrevious).card :=
  ClassClosure.generateCounted_checks_le_family_card
    profile registration zeroPrevious

theorem visible_work_is_polynomial :
    visibleGeneration.checks <=
      (ClassClosure.Generated.workBudget profile registration visiblePrevious).coefficient *
        ((ClassClosure.Generated.workBudget profile registration visiblePrevious).size
          visibleGeneration.value + 1) ^
        (ClassClosure.Generated.workBudget profile registration visiblePrevious).degree :=
  ClassClosure.generateCounted_checks_le_polynomial
    profile registration visiblePrevious

def visibleOutput : ClassClosure.TargetVisibleOutput profile visiblePrevious :=
  visibleGeneration.value.targetVisibleResidual visible_terminal

theorem visible_output_is_exact_first_hit :
    visibleOutput.residual.hit.index.1 = 1 := by
  decide

theorem visible_output_is_live :
    visibleOutput.residual.hit.value = .live := by
  have visible := visibleOutput.residual.targetVisible
  change project visibleOutput.residual.hit.value = true at visible
  cases equal : visibleOutput.residual.hit.value with
  | closed => simp [project, equal] at visible
  | pending => simp [project, equal] at visible
  | live => exact equal

theorem visible_output_is_nonzero :
    Not (project visibleOutput.residual.hit.value = false) :=
  visibleOutput.residual.quotientNonzero

def zeroOutput :
    ClassClosure.ZeroQuotientOutput profile registration zeroPrevious :=
  zeroGeneration.value.zeroQuotientPropagation zero_terminal

theorem pending_is_registered_by_zero_output :
    Carrier.pending ∈
      (profile.extendedLedger zeroPrevious zeroOutput.avoids).classes :=
  zeroOutput.propagation.representedFamilyIncluded (by
    change Carrier.pending ∈ [Carrier.pending, Carrier.closed]
    simp)

/-- The finite miss alone does not claim that the ambient Bool quotient is
zero: the omitted live carrier still represents its nonnull class. -/
theorem zero_family_is_not_target_complete :
    Not (ClassClosure.TargetComplete profile) := by
  intro complete
  have quotientZero : ClassClosure.BoundaryZero profile zeroPrevious :=
    zeroOutput.boundaryZero complete
  have impossible : true = false := quotientZero true
  exact Bool.noConfusion impossible

namespace CompleteZero

def closure : Core.ClosureOperator Unit :=
  Core.ClosureOperator.identity Unit

def targetNull (_carrier : Unit) : Prop :=
  True

def ledger : ClosedClassLedger closure targetNull where
  classes := Set.univ
  closed := rfl
  targetNull := by simp [targetNull]

def quotientUniversal : QuotientUniversalProperty (fun _carrier : Unit => ()) where
  descend := fun map _compatible _quotientClass => map ()
  descend_project := by intros; rfl
  descend_unique := by
    intro Result map compatible candidate commutes quotientClass
    cases quotientClass
    exact commutes ()

def quotient : LedgerQuotient ledger where
  Quotient := Unit
  project := fun _carrier => ()
  null := ()
  killsClosed := by intros; rfl
  universal := quotientUniversal

abbrev Previous := Residual.Ledger Unit

def previous : Previous :=
  Residual.Ledger.initial ()

def family : Finite.Enumeration Unit :=
  Finite.Enumeration.singleton ()

def profile : ClassClosure.Profile Previous where
  Carrier := Unit
  closure := closure
  TargetNull := targetNull
  family := (Residual.Query.residual (Source := Previous) (Residual := Unit)).map
    fun _previous _residual => family
  ledger := (Residual.Query.residual (Source := Previous) (Residual := Unit)).map
    fun _previous _residual => ledger
  quotient := fun _previous => quotient
  TargetVisible := fun _previous _quotientClass => False
  targetVisibleDecidable := fun _previous _quotientClass => isFalse id
  visibleNonzero := by simp
  nullOfNotVisible := by intros; rfl
  targetNullOfNull := by simp [targetNull]
  closureStable := ClosureStable.identity

def complete : ClassClosure.TargetComplete profile where
  representsNonzero := by
    intro previous quotientClass nonzero
    exact (nonzero (by cases quotientClass; rfl)).elim

def nextQuotient (current : Previous)
    (avoids : profile.AvoidsTargetVisible current) :
    LedgerQuotient (profile.extendedLedger current avoids) where
  Quotient := Unit
  project := fun _carrier => ()
  null := ()
  killsClosed := by intros; rfl
  universal := quotientUniversal

def registration : ClassClosure.ExtensionRegistration profile where
  nextQuotient := nextQuotient
  quotientTransport := fun _previous _avoids _quotientClass => ()
  quotientTransport_project := by intros; rfl
  quotientTransport_null := by intros; rfl

def generation :=
  ClassClosure.generateCounted profile registration previous

theorem terminal_is_zero : generation.value.terminal = .zeroQuotient := by
  decide

def output : ClassClosure.ZeroQuotientOutput profile registration previous :=
  generation.value.zeroQuotientPropagation terminal_is_zero

theorem generated_whole_quotient_is_zero :
    ClassClosure.BoundaryZero profile previous :=
  output.boundaryZero complete

end CompleteZero

/-- A downstream executor can retain the generated branch in one extension of
its own literal predecessor. -/
abbrev EmbeddedStage := Residual.Ledger.Extension Previous fun previous =>
  ClassClosure.Generated profile registration previous

def embedCounted (previous : Previous) : Counted EmbeddedStage :=
  (ClassClosure.generateCounted profile registration previous).map
    (Residual.Ledger.extend previous)

theorem embedded_previous_is_literal :
    (embedCounted visiblePrevious).value.previous = visiblePrevious :=
  rfl

theorem embedding_preserves_exact_checks :
    (embedCounted visiblePrevious).checks = visibleGeneration.checks :=
  rfl

def stagedRun :=
  ClassClosure.run profile registration visiblePrevious

theorem staged_run_still_uses_literal_predecessor :
    stagedRun.previous.previous = visiblePrevious :=
  ClassClosure.run_previous profile registration visiblePrevious

theorem staged_run_matches_generated_terminal :
    ClassClosure.terminal stagedRun = visibleGeneration.value.terminal :=
  ClassClosure.run_terminal_eq_generated profile registration visiblePrevious

#print axioms ClassClosure.generateCounted
#print axioms ClassClosure.generateCounted_checks
#print axioms ClassClosure.generateCounted_checks_le_family_card
#print axioms ClassClosure.generateCounted_checks_le_polynomial
#print axioms visible_output_is_exact_first_hit
#print axioms pending_is_registered_by_zero_output
#print axioms zero_family_is_not_target_complete
#print axioms CompleteZero.generated_whole_quotient_is_zero

end Hypostructure.Fixtures.ClassClosureCounted
