import Hypostructure.Core.ClosedLedger.Quotient

/-!
# Closed-ledger propagation

A propagation transports one accumulated ledger to a new carrier, registers
the enlarged quotient there, and supplies the induced map between quotients.
Core composes such registrations and proves that earlier classes stay null.
-/

namespace Hypostructure.Core

universe uCarrier uQuotient uNextCarrier uNextQuotient

/-- A represented, quotient-compatible transport of a closed ledger to the
next carrier in a proof program. -/
structure LedgerPropagation
    {Carrier : Type uCarrier} {C : ClosureOperator Carrier}
    {TargetNull : Carrier -> Prop} (L : ClosedClassLedger C TargetNull)
    (Q : LedgerQuotient.{uCarrier, uQuotient} L) where
  NextCarrier : Type uNextCarrier
  nextClosure : ClosureOperator NextCarrier
  nextTargetNull : NextCarrier -> Prop
  transport : Carrier -> NextCarrier
  nextLedger : ClosedClassLedger nextClosure nextTargetNull
  nextQuotient : LedgerQuotient.{uNextCarrier, uNextQuotient} nextLedger
  includesTransport : forall {x}, x ∈ L.classes ->
    transport x ∈ nextLedger.classes
  quotientTransport : Q.Quotient -> nextQuotient.Quotient
  quotientTransport_project : forall x,
    quotientTransport (Q.project x) = nextQuotient.project (transport x)
  quotientTransport_null : quotientTransport Q.null = nextQuotient.null

namespace LedgerPropagation

variable {Carrier : Type uCarrier} {C : ClosureOperator Carrier}
  {TargetNull : Carrier -> Prop} {L : ClosedClassLedger C TargetNull}
  {Q : LedgerQuotient.{uCarrier, uQuotient} L}

/-- A prior closed class remains target-null after transport.  No proof of its
domain-specific closing estimate is requested again. -/
theorem priorClosedClassesRemainTargetNull
    (P : LedgerPropagation.{uCarrier, uQuotient, uNextCarrier, uNextQuotient}
      L Q) {x : Carrier} (closed : x ∈ L.classes) :
    P.nextTargetNull (P.transport x) :=
  P.nextLedger.targetNull (P.includesTransport closed)

/-- The no-rechecking theorem: every prior closed class is killed by the next
registered quotient solely through ledger inclusion. -/
theorem priorClosedClassesRemainKilled
    (P : LedgerPropagation.{uCarrier, uQuotient, uNextCarrier, uNextQuotient}
      L Q) {x : Carrier} (closed : x ∈ L.classes) :
    P.nextQuotient.project (P.transport x) = P.nextQuotient.null :=
  P.nextQuotient.killsClosed (P.includesTransport closed)

/-- Both persistent facts exported by propagation: transported target-nullity
and a zero image in the enlarged quotient. -/
theorem noRechecking
    (P : LedgerPropagation.{uCarrier, uQuotient, uNextCarrier, uNextQuotient}
      L Q) {x : Carrier} (closed : x ∈ L.classes) :
    P.nextTargetNull (P.transport x) ∧
      P.nextQuotient.project (P.transport x) = P.nextQuotient.null :=
  ⟨P.priorClosedClassesRemainTargetNull closed,
    P.priorClosedClassesRemainKilled closed⟩

/-- Compose two consecutive carrier and quotient transports.  This is the
framework operation used to iterate ledger propagation. -/
def andThen
    (first : LedgerPropagation.{uCarrier, uQuotient, uNextCarrier,
      uNextQuotient} L Q)
    (second : LedgerPropagation first.nextLedger first.nextQuotient) :
    LedgerPropagation L Q where
  NextCarrier := second.NextCarrier
  nextClosure := second.nextClosure
  nextTargetNull := second.nextTargetNull
  transport := fun x => second.transport (first.transport x)
  nextLedger := second.nextLedger
  nextQuotient := second.nextQuotient
  includesTransport := fun closed =>
    second.includesTransport (first.includesTransport closed)
  quotientTransport := fun q =>
    second.quotientTransport (first.quotientTransport q)
  quotientTransport_project := by
    intro x
    rw [first.quotientTransport_project, second.quotientTransport_project]
  quotientTransport_null := by
    rw [first.quotientTransport_null, second.quotientTransport_null]

/-- The no-rechecking theorem remains available after any composed pair of
propagations. -/
theorem priorClosedClassesRemainKilled_after_then
    (first : LedgerPropagation.{uCarrier, uQuotient, uNextCarrier,
      uNextQuotient} L Q)
    (second : LedgerPropagation first.nextLedger first.nextQuotient)
    {x : Carrier} (closed : x ∈ L.classes) :
    (first.andThen second).nextQuotient.project
        ((first.andThen second).transport x) =
      (first.andThen second).nextQuotient.null :=
  (first.andThen second).priorClosedClassesRemainKilled closed

end LedgerPropagation

end Hypostructure.Core
