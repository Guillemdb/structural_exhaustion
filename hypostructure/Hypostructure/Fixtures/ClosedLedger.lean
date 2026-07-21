import Hypostructure.Core.ClosedLedger.Propagation

/-!
# Closed-ledger fixtures

An identity-closure carrier contains three target-null classes and one live
class.  Two extensions successively kill the second and third classes.  The
domain supplies concrete quotients with four, three, and two classes; Core
composes the two propagations and retains the original kill certificates.
-/

namespace Hypostructure.Fixtures.ClosedLedger

open Hypostructure.Core

inductive Carrier where
  | closed0
  | closed1
  | closed2
  | survivor
deriving DecidableEq

def targetNull : Carrier -> Prop
  | .closed0 | .closed1 | .closed2 => True
  | .survivor => False

def closure : ClosureOperator Carrier :=
  ClosureOperator.identity Carrier

def targetNullStable : ClosureStable closure targetNull :=
  ClosureStable.identity

def class0 : Set Carrier := {x | x = .closed0}
def class1 : Set Carrier := {x | x = .closed1}
def class2 : Set Carrier := {x | x = .closed2}

def class1TargetNull : forall {x}, x ∈ class1 -> targetNull x := by
  intro x hx
  subst x
  trivial

def class2TargetNull : forall {x}, x ∈ class2 -> targetNull x := by
  intro x hx
  subst x
  trivial

def initialLedger : ClosedClassLedger closure targetNull where
  classes := class0
  closed := rfl
  targetNull := by
    intro x hx
    subst x
    trivial

def class1Ledger : ClosedClassLedger closure targetNull where
  classes := class1
  closed := rfl
  targetNull := class1TargetNull

/-- Union and extension agree for these already-closed identity classes. -/
theorem union_matches_first_extension :
    initialLedger.union class1Ledger targetNullStable =
      initialLedger.extend targetNullStable class1 class1TargetNull :=
  rfl

def firstLedger : ClosedClassLedger closure targetNull :=
  initialLedger.extend targetNullStable class1 class1TargetNull

def secondLedger : ClosedClassLedger closure targetNull :=
  firstLedger.extend targetNullStable class2 class2TargetNull

@[simp] theorem mem_initialLedger (x : Carrier) :
    x ∈ initialLedger.classes ↔ x = .closed0 :=
  Iff.rfl

@[simp] theorem mem_firstLedger (x : Carrier) :
    x ∈ firstLedger.classes ↔ x = .closed0 ∨ x = .closed1 :=
  Iff.rfl

@[simp] theorem mem_secondLedger (x : Carrier) :
    x ∈ secondLedger.classes ↔
      (x = .closed0 ∨ x = .closed1) ∨ x = .closed2 :=
  Iff.rfl

/-! ## Domain-supplied quotient universal properties -/

def initialQuotient : LedgerQuotient initialLedger where
  Quotient := Carrier
  project := id
  null := .closed0
  killsClosed := by
    intro x hx
    exact hx
  universal := {
    descend := fun map _ => map
    descend_project := by intros; rfl
    descend_unique := by
      intro Result map compatible candidate commutes q
      exact commutes q
  }

inductive FirstQuotient where
  | killed
  | pending
  | live
deriving DecidableEq

def firstProject : Carrier -> FirstQuotient
  | .closed0 | .closed1 => .killed
  | .closed2 => .pending
  | .survivor => .live

def firstUniversal : QuotientUniversalProperty firstProject where
  descend := fun map _ q =>
    match q with
    | .killed => map .closed0
    | .pending => map .closed2
    | .live => map .survivor
  descend_project := by
    intro Result map compatible x
    cases x with
    | closed0 => rfl
    | closed1 =>
        exact compatible (x := Carrier.closed0) (y := Carrier.closed1) rfl
    | closed2 => rfl
    | survivor => rfl
  descend_unique := by
    intro Result map compatible candidate commutes q
    cases q with
    | killed => exact commutes .closed0
    | pending => exact commutes .closed2
    | live => exact commutes .survivor

def firstQuotient : LedgerQuotient firstLedger where
  Quotient := FirstQuotient
  project := firstProject
  null := .killed
  killsClosed := by
    intro x hx
    change x = .closed0 ∨ x = .closed1 at hx
    rcases hx with rfl | rfl <;> rfl
  universal := firstUniversal

inductive SecondQuotient where
  | killed
  | live
deriving DecidableEq

def secondProject : Carrier -> SecondQuotient
  | .closed0 | .closed1 | .closed2 => .killed
  | .survivor => .live

def secondUniversal : QuotientUniversalProperty secondProject where
  descend := fun map _ q =>
    match q with
    | .killed => map .closed0
    | .live => map .survivor
  descend_project := by
    intro Result map compatible x
    cases x with
    | closed0 => rfl
    | closed1 =>
        exact compatible (x := Carrier.closed0) (y := Carrier.closed1) rfl
    | closed2 =>
        exact compatible (x := Carrier.closed0) (y := Carrier.closed2) rfl
    | survivor => rfl
  descend_unique := by
    intro Result map compatible candidate commutes q
    cases q with
    | killed => exact commutes .closed0
    | live => exact commutes .survivor

def secondQuotient : LedgerQuotient secondLedger where
  Quotient := SecondQuotient
  project := secondProject
  null := .killed
  killsClosed := by
    intro x hx
    change (x = .closed0 ∨ x = .closed1) ∨ x = .closed2 at hx
    rcases hx with (rfl | rfl) | rfl <;> rfl
  universal := secondUniversal

/-! ## Two quotient-compatible propagations -/

def firstPropagation : LedgerPropagation initialLedger initialQuotient where
  NextCarrier := Carrier
  nextClosure := closure
  nextTargetNull := targetNull
  transport := id
  nextLedger := firstLedger
  nextQuotient := firstQuotient
  includesTransport := by
    intro x hx
    exact initialLedger.subset_extend targetNullStable class1
      class1TargetNull hx
  quotientTransport := firstProject
  quotientTransport_project := by intros; rfl
  quotientTransport_null := rfl

def secondQuotientTransport : FirstQuotient -> SecondQuotient
  | .killed | .pending => .killed
  | .live => .live

def secondPropagation : LedgerPropagation firstLedger firstQuotient where
  NextCarrier := Carrier
  nextClosure := closure
  nextTargetNull := targetNull
  transport := id
  nextLedger := secondLedger
  nextQuotient := secondQuotient
  includesTransport := by
    intro x hx
    exact firstLedger.subset_extend targetNullStable class2
      class2TargetNull hx
  quotientTransport := secondQuotientTransport
  quotientTransport_project := by
    intro x
    cases x <;> rfl
  quotientTransport_null := rfl

def twoPropagations : LedgerPropagation initialLedger initialQuotient :=
  firstPropagation.andThen secondPropagation

/-- The original closed class is still killed after two propagations, with no
new class-specific target-null proof supplied to this theorem. -/
theorem initialClassKilledAfterTwo {x : Carrier}
    (closed : x ∈ initialLedger.classes) :
    twoPropagations.nextQuotient.project (twoPropagations.transport x) =
      twoPropagations.nextQuotient.null :=
  twoPropagations.priorClosedClassesRemainKilled closed

/-- Every class accumulated before the second propagation remains both
target-null and killed. -/
theorem firstLedgerNeedsNoRechecking {x : Carrier}
    (closed : x ∈ firstLedger.classes) :
    targetNull x ∧ secondProject x = .killed :=
  secondPropagation.noRechecking closed

/-! ## A later invariant factors through the twice-reduced quotient -/

def quotientReadout : SecondQuotient -> Bool
  | .killed => false
  | .live => true

def survivorInvariant (x : Carrier) : Bool :=
  quotientReadout (secondProject x)

def survivorInvariantDescends :
    LaterInvariantDescends secondQuotient Bool survivorInvariant where
  compatible := by
    intro x y equalProjection
    exact congrArg quotientReadout equalProjection

theorem survivorInvariant_factors (q : SecondQuotient) :
    quotientReadout q = survivorInvariantDescends.factor q :=
  survivorInvariantDescends.factor_unique quotientReadout (by
    intro x
    rfl) q

#print axioms union_matches_first_extension
#print axioms initialClassKilledAfterTwo
#print axioms firstLedgerNeedsNoRechecking
#print axioms survivorInvariant_factors

end Hypostructure.Fixtures.ClosedLedger
