import Hypostructure.Core.NormalForm.ClassClosure
import Hypostructure.Core.NormalForm.EqualityRigidity
import Hypostructure.Core.NormalForm.SignGap

/-!
# Domain-independent normal-form fixtures

Finite class and scalar models exercise every normal-form terminal, exact
predecessor retention, closed-ledger propagation, optional separator inputs,
direct quantitative closure, and compact equality/minimizing descendants.
-/

namespace Hypostructure.Fixtures.NormalForms

open Hypostructure.Core
open Core.NormalForm

namespace ClassModel

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

def stable : ClosureStable closure targetNull :=
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
  separator : Option Bool

abbrev Previous := Residual.Ledger Residual

def residualQuery : Residual.Query Previous fun _previous => Residual :=
  Residual.Query.residual

def familyQuery : Residual.Query Previous fun _previous =>
    Finite.Enumeration Carrier :=
  residualQuery.map fun _previous residual => residual.family

def ledgerQuery : Residual.Query Previous fun _previous =>
    ClosedClassLedger closure targetNull :=
  residualQuery.map fun _previous _residual => initialLedger

def classProfile : ClassClosure.Profile Previous where
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
    cases value : project carrier with
    | false => exact value
    | true => exact (invisible value).elim
  targetNullOfNull := by
    intro previous carrier equalNull
    exact equalNull
  closureStable := stable

def nextQuotient (previous : Previous)
    (avoids : classProfile.AvoidsTargetVisible previous) :
    LedgerQuotient (classProfile.extendedLedger previous avoids) where
  Quotient := Bool
  project := project
  null := false
  killsClosed := by
    intro carrier closed
    exact (classProfile.extendedLedger previous avoids).targetNull closed
  universal := quotientUniversal

def classRegistration : ClassClosure.ExtensionRegistration classProfile where
  nextQuotient := nextQuotient
  quotientTransport := fun _previous _avoids => id
  quotientTransport_project := by intros; rfl
  quotientTransport_null := by intros; rfl

def zeroResidual : Residual where
  family := Finite.Enumeration.singleton .pending
  separator := none

def visibleResidual : Residual where
  family := Finite.Enumeration.singleton .live
  separator := some true

def zeroPrevious : Previous := Residual.Ledger.initial zeroResidual
def visiblePrevious : Previous := Residual.Ledger.initial visibleResidual

def zeroAvoids : classProfile.AvoidsTargetVisible zeroPrevious := by
  intro index visible
  have member := (classProfile.familyAt zeroPrevious).get_mem index
  have equal : (classProfile.familyAt zeroPrevious).get index =
      Carrier.pending := by
    change (classProfile.familyAt zeroPrevious).get index ∈
      [Carrier.pending] at member
    exact List.mem_singleton.mp member
  change project ((classProfile.familyAt zeroPrevious).get index) = true at visible
  rw [equal] at visible
  contradiction

def visibleHasTarget : classProfile.HasTargetVisible visiblePrevious := by
  change (classProfile.scan visiblePrevious).HasHit
  apply Finite.Search.complete
  refine ⟨Carrier.live, ?_, rfl⟩
  change Carrier.live ∈ [Carrier.live]
  simp

def classZeroResult :=
  ClassClosure.run classProfile classRegistration zeroPrevious

def classVisibleResult :=
  ClassClosure.run classProfile classRegistration visiblePrevious

theorem class_zero_previous :
    classZeroResult.previous.previous = zeroPrevious :=
  rfl

theorem class_zero_terminal :
    ClassClosure.terminal classZeroResult = .zeroQuotient := by
  decide

theorem class_visible_previous :
    classVisibleResult.previous.previous = visiblePrevious :=
  rfl

theorem class_visible_terminal :
    ClassClosure.terminal classVisibleResult = .targetVisible := by
  decide

def zeroPropagation :=
  ClassClosure.zeroPropagation classProfile classRegistration zeroPrevious
    zeroAvoids

theorem represented_pending_is_propagated :
    Carrier.pending ∈
      (classProfile.extendedLedger zeroPrevious zeroAvoids).classes :=
  zeroPropagation.representedFamilyIncluded (by
    change Carrier.pending ∈ [Carrier.pending]
    simp)

theorem prior_closed_class_stays_killed :
    zeroPropagation.propagation.nextQuotient.project
        (zeroPropagation.propagation.transport Carrier.closed) =
      zeroPropagation.propagation.nextQuotient.null :=
  zeroPropagation.priorClassRemainsKilled (by rfl)

def exactVisibleClass :=
  ClassClosure.targetVisibleResidual classProfile visiblePrevious
    visibleHasTarget

theorem exact_visible_class_is_live :
    exactVisibleClass.hit.value = Carrier.live := by
  have member := exactVisibleClass.hit.member
  change exactVisibleClass.hit.value ∈ [Carrier.live] at member
  exact List.mem_singleton.mp member

theorem exact_visible_class_nonzero :
    Not (project exactVisibleClass.hit.value = false) :=
  exactVisibleClass.quotientNonzero

/-! ## Equality-rigidity reuses the class executor -/

def separatorQuery : Residual.Query Previous fun _previous => Option PUnit :=
  residualQuery.map fun _previous residual =>
    residual.separator.map fun _value => PUnit.unit

def saturationQuery : Residual.Query Previous fun _previous => PUnit :=
  residualQuery.map fun _previous _residual => PUnit.unit

theorem visible_projection_nonzero {carrier : Carrier}
    (visible : initialQuotient.project carrier = true) :
    Not (initialQuotient.project carrier = false) := by
  cases carrier <;> simp_all [initialQuotient, project]

theorem invisible_projection_null {carrier : Carrier}
    (invisible : Not (initialQuotient.project carrier = true)) :
    initialQuotient.project carrier = false := by
  cases carrier <;> simp_all [initialQuotient, project]

def equalityProfile : EqualityRigidity.Profile Previous where
  Carrier := Carrier
  closure := closure
  TargetNull := targetNull
  equalityFamily := familyQuery
  ledger := ledgerQuery
  quotient := fun _previous => initialQuotient
  Saturation := fun _previous => PUnit
  saturation := saturationQuery
  Separator := fun _previous => PUnit
  separator := separatorQuery
  RigidityVisible := fun _previous _saturation separator quotientClass =>
    match separator with
    | none => quotientClass = true
    | some _ => quotientClass = true
  rigidityVisibleDecidable := by
    intro previous quotientClass
    cases separatorQuery.read previous <;> exact Bool.decEq quotientClass true
  visibleNonzero := by
    intro previous carrier visible equalNull
    cases separator : separatorQuery.read previous with
    | none =>
        rw [separator] at visible
        exact visible_projection_nonzero visible equalNull
    | some value =>
        rw [separator] at visible
        exact visible_projection_nonzero visible equalNull
  nullOfNotVisible := by
    intro previous carrier invisible
    cases separator : separatorQuery.read previous with
    | none =>
        rw [separator] at invisible
        exact invisible_projection_null invisible
    | some value =>
        rw [separator] at invisible
        exact invisible_projection_null invisible
  targetNullOfNull := by
    intro previous carrier equalNull
    exact equalNull
  closureStable := stable

def equalityNextQuotient (previous : Previous)
    (avoids : equalityProfile.toClassClosure.AvoidsTargetVisible previous) :
    LedgerQuotient
      (equalityProfile.toClassClosure.extendedLedger previous avoids) where
  Quotient := Bool
  project := project
  null := false
  killsClosed := by
    intro carrier closed
    exact (equalityProfile.toClassClosure.extendedLedger previous avoids).targetNull
      closed
  universal := quotientUniversal

def equalityRegistration :
    EqualityRigidity.ExtensionRegistration equalityProfile where
  nextQuotient := equalityNextQuotient
  quotientTransport := fun _previous _avoids => id
  quotientTransport_project := by intros; rfl
  quotientTransport_null := by intros; rfl

def equalityZeroResult :=
  EqualityRigidity.run equalityProfile equalityRegistration zeroPrevious

def equalityVisibleResult :=
  EqualityRigidity.run equalityProfile equalityRegistration visiblePrevious

theorem equality_zero_terminal :
    EqualityRigidity.terminal equalityZeroResult =
      .zeroEqualityQuotient := by
  decide

theorem equality_visible_terminal :
    EqualityRigidity.terminal equalityVisibleResult =
      .targetVisibleRigidity := by
  decide

theorem equality_none_separator_consumed :
    separatorQuery.read zeroPrevious = none :=
  rfl

theorem equality_some_separator_consumed :
    separatorQuery.read visiblePrevious = some PUnit.unit :=
  rfl

end ClassModel

namespace ScalarModel

inductive Mode where
  | subcritical
  | feeding
  | equality
  | zeroGap
  deriving DecidableEq, Repr

def problem : Core.Problem where
  Ambient := PUnit
  Baseline := fun _ambient => True
  BranchState := fun _ambient => PUnit

def extraction : Core.CompactExtraction problem where
  Sequence := Mode
  Limit := PUnit
  Topology := PUnit
  term := fun _sequence _index => PUnit.unit
  realizeLimit := fun _limit => PUnit.unit
  Extracted := fun _sequence => PUnit
  selector := fun _extracted index => index
  selectorStrict := fun _extracted => strictMono_id
  limit := fun _extracted => PUnit.unit
  topology := fun _extracted => PUnit.unit
  Converges := fun _sequence _extracted _topology => True
  convergence := fun _extracted => trivial
  extract := fun _sequence => PUnit.unit

def budget : ResourceBudget where
  Resource := Nat
  le := (· <= ·)
  leRefl := Nat.le_refl
  leTrans := Nat.le_trans
  zero := 0
  add := (· + ·)
  ceiling := id
  zeroLe := Nat.zero_le
  addMono := Nat.add_le_add
  addAssoc := Nat.add_assoc
  zeroAdd := Nat.zero_add
  addZero := Nat.add_zero

abbrev Previous := Residual.Ledger Mode

def modeQuery : Residual.Query Previous fun _previous => Mode :=
  Residual.Query.residual

def loss : Mode -> Nat
  | .subcritical => 2
  | .feeding => 1
  | .equality | .zeroGap => 1

def readout : Mode -> Nat
  | .subcritical => 1
  | .feeding => 2
  | .equality | .zeroGap => 1

def gap : Mode -> Nat
  | .subcritical | .feeding | .equality => 1
  | .zeroGap => 0

def data : SignGap.Data extraction budget Previous where
  family := modeQuery
  loss := fun _previous mode => loss mode
  readout := fun _previous mode => readout mode
  gap := fun _previous mode => gap mode
  Normalized := fun previous mode => mode = modeQuery.read previous
  normalized := by intros; rfl
  lossNonnegative := by intros; exact Nat.zero_le _
  readoutPositive := by
    intro previous
    cases modeQuery.read previous with
    | subcritical =>
        change (0 : Nat) <= 1 ∧ Not (1 <= 0)
        omega
    | feeding =>
        change (0 : Nat) <= 2 ∧ Not (2 <= 0)
        omega
    | equality =>
        change (0 : Nat) <= 1 ∧ Not (1 <= 0)
        omega
    | zeroGap =>
        change (0 : Nat) <= 1 ∧ Not (1 <= 0)
        omega
  gapNonnegative := by intros; exact Nat.zero_le _

def comparison : SignGap.ExactComparison data where
  Subcritical := fun previous => modeQuery.read previous = .subcritical
  Feeding := fun previous => modeQuery.read previous = .feeding
  Equality := fun previous => modeQuery.read previous = .equality
  ZeroGap := fun previous => modeQuery.read previous = .zeroGap
  subcriticalDecidable := fun _previous => inferInstance
  feedingDecidable := fun _previous => inferInstance
  equalityDecidable := fun _previous => inferInstance
  subcriticalSound := by
    intro previous proof
    change modeQuery.read previous = Mode.subcritical at proof
    change SignGap.StrictlyBelow budget
        (readout (modeQuery.read previous)) (loss (modeQuery.read previous)) ∨
      SignGap.StrictlyBelow budget budget.zero
        (gap (modeQuery.read previous))
    rw [proof]
    apply Or.inl
    change (1 : Nat) <= 2 ∧ Not (2 <= 1)
    omega
  feedingSound := by
    intro previous proof
    change modeQuery.read previous = Mode.feeding at proof
    change SignGap.StrictlyBelow budget
      (loss (modeQuery.read previous)) (readout (modeQuery.read previous))
    rw [proof]
    change (1 : Nat) <= 2 ∧ Not (2 <= 1)
    omega
  equalitySound := by
    intro previous proof
    change modeQuery.read previous = Mode.equality at proof
    change loss (modeQuery.read previous) = readout (modeQuery.read previous)
    rw [proof]
    rfl
  zeroGapSound := by
    intro previous proof
    change modeQuery.read previous = Mode.zeroGap at proof
    change gap (modeQuery.read previous) = budget.zero
    rw [proof]
    rfl
  exhaustive := by
    intro previous
    cases modeQuery.read previous <;> simp
  subcriticalDisjoint := by
    intro previous subcritical remainder
    rcases remainder with feeding | equality | zeroGap <;> simp_all
  feedingDisjoint := by
    intro previous feeding remainder
    rcases remainder with equality | zeroGap <;> simp_all
  equalityDisjoint := by
    intro previous equality zeroGap
    simp_all

def baselineClosed : extraction.BaselineClosed where
  closed := by intros; trivial

def equalityRetained (_ambient : PUnit) : Prop := True
def minimizingRetained (_ambient : PUnit) : Prop := True

def equalityPersistent :
    extraction.ObstructionPersistent equalityRetained where
  closed := by intros; trivial

def minimizingPersistent :
    extraction.ObstructionPersistent minimizingRetained where
  closed := by intros; trivial

def equalityInput (previous : Previous)
    (_proof : comparison.Equality previous) :
    extraction.RetainedInput equalityRetained (data.familyAt previous) where
  baseline := by intros; trivial
  obstruction := by intros; trivial

def minimizingInput (previous : Previous)
    (_proof : comparison.ZeroGap previous) :
    extraction.RetainedInput minimizingRetained (data.familyAt previous) where
  baseline := by intros; trivial
  obstruction := by intros; trivial

def profile : SignGap.Profile.{0, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    extraction budget Previous where
  data := data
  comparison := comparison
  Estimate := fun _previous => True
  estimate := by intros; trivial
  EqualityRetained := equalityRetained
  MinimizingRetained := minimizingRetained
  baselineClosed := baselineClosed
  equalityPersistent := equalityPersistent
  minimizingPersistent := minimizingPersistent
  equalityInput := by
    intro previous _proof
    exact {
      baseline := by intros; trivial
      obstruction := by intros; trivial
    }
  minimizingInput := by
    intro previous _proof
    exact {
      baseline := by intros; trivial
      obstruction := by intros; trivial
    }

def subcriticalPrevious : Previous :=
  Residual.Ledger.initial .subcritical

def feedingPrevious : Previous :=
  Residual.Ledger.initial .feeding

def equalityPrevious : Previous :=
  Residual.Ledger.initial .equality

def zeroGapPrevious : Previous :=
  Residual.Ledger.initial .zeroGap

def subcriticalResult := SignGap.run profile subcriticalPrevious
def feedingResult := SignGap.run profile feedingPrevious
def equalityResult := SignGap.run profile equalityPrevious
def zeroGapResult := SignGap.run profile zeroGapPrevious

theorem sign_subcritical_previous :
    subcriticalResult.previous = subcriticalPrevious :=
  rfl

theorem sign_subcritical_terminal :
    subcriticalResult.added.terminal = .subcritical :=
  rfl

theorem sign_feeding_terminal :
    feedingResult.added.terminal = .feeding :=
  rfl

theorem sign_equality_terminal :
    equalityResult.added.terminal = .equality :=
  rfl

theorem sign_zero_gap_terminal :
    zeroGapResult.added.terminal = .zeroGap :=
  rfl

theorem equality_descendant_is_baseline :
    problem.Baseline
      (extraction.descend baselineClosed equalityPersistent .equality
        (equalityInput equalityPrevious rfl)).record.descendant :=
  trivial

theorem minimizing_descendant_is_retained :
    minimizingRetained
      (extraction.descend baselineClosed minimizingPersistent .zeroGap
        (minimizingInput zeroGapPrevious rfl)).record.descendant :=
  trivial

end ScalarModel

#print axioms ClassClosure.run
#print axioms EqualityRigidity.run
#print axioms SignGap.run
#print axioms ClassModel.class_zero_previous
#print axioms ClassModel.class_zero_terminal
#print axioms ClassModel.class_visible_terminal
#print axioms ClassModel.represented_pending_is_propagated
#print axioms ClassModel.prior_closed_class_stays_killed
#print axioms ClassModel.exact_visible_class_nonzero
#print axioms ClassModel.equality_zero_terminal
#print axioms ClassModel.equality_visible_terminal
#print axioms ClassModel.equality_none_separator_consumed
#print axioms ClassModel.equality_some_separator_consumed
#print axioms ScalarModel.sign_subcritical_terminal
#print axioms ScalarModel.sign_feeding_terminal
#print axioms ScalarModel.sign_equality_terminal
#print axioms ScalarModel.sign_zero_gap_terminal
#print axioms ScalarModel.equality_descendant_is_baseline
#print axioms ScalarModel.minimizing_descendant_is_retained

end Hypostructure.Fixtures.NormalForms
