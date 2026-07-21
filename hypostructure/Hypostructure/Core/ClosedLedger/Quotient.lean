import Hypostructure.Core.ClosedLedger.Closure

/-!
# Quotients by closed-class ledgers

A domain registers the quotient type, its projection, the class representing
the killed ledger, and the projection's universal property.  Core uses that
interface to descend later invariants without knowing the quotient's algebraic
or topological construction.
-/

namespace Hypostructure.Core

universe uCarrier uQuotient uResult

/-- A carrier map is compatible with a projection when it is constant on the
projection fibres. -/
def ProjectionCompatible {Carrier : Type uCarrier} {Quotient : Type uQuotient}
    {Result : Type uResult} (project : Carrier -> Quotient)
    (map : Carrier -> Result) : Prop :=
  forall {x y}, project x = project y -> map x = map y

/-- Factorization and uniqueness for a quotient projection.  The result
universe covers both the carrier and quotient universes used by this
registration. -/
structure QuotientUniversalProperty {Carrier : Type uCarrier}
    {Quotient : Type uQuotient} (project : Carrier -> Quotient) where
  descend : {Result : Type (max uCarrier uQuotient)} ->
    (map : Carrier -> Result) -> ProjectionCompatible project map ->
      Quotient -> Result
  descend_project : forall {Result : Type (max uCarrier uQuotient)}
    (map : Carrier -> Result) (compatible : ProjectionCompatible project map)
    (x : Carrier), descend map compatible (project x) = map x
  descend_unique : forall {Result : Type (max uCarrier uQuotient)}
    (map : Carrier -> Result) (compatible : ProjectionCompatible project map)
    (candidate : Quotient -> Result),
    (forall x, candidate (project x) = map x) ->
      forall q, candidate q = descend map compatible q

/-- A domain-supplied quotient of a closed ledger.  `null` is the quotient
class to which every previously closed carrier object projects. -/
structure LedgerQuotient {Carrier : Type uCarrier}
    {C : ClosureOperator Carrier} {TargetNull : Carrier -> Prop}
    (L : ClosedClassLedger C TargetNull) where
  Quotient : Type uQuotient
  project : Carrier -> Quotient
  null : Quotient
  killsClosed : forall {x}, x ∈ L.classes -> project x = null
  universal : QuotientUniversalProperty project

namespace LedgerQuotient

variable {Carrier : Type uCarrier} {C : ClosureOperator Carrier}
  {TargetNull : Carrier -> Prop} {L : ClosedClassLedger C TargetNull}

/-- The canonical projection exported by a registered ledger quotient. -/
abbrev canonicalProjection (Q : LedgerQuotient.{uCarrier, uQuotient} L) :
    Carrier -> Q.Quotient :=
  Q.project

/-- Core's canonical factor of a projection-compatible map. -/
def descend (Q : LedgerQuotient.{uCarrier, uQuotient} L)
    {Result : Type (max uCarrier uQuotient)} (map : Carrier -> Result)
    (compatible : ProjectionCompatible Q.project map) : Q.Quotient -> Result :=
  Q.universal.descend map compatible

@[simp] theorem descend_project
    (Q : LedgerQuotient.{uCarrier, uQuotient} L)
    {Result : Type (max uCarrier uQuotient)} (map : Carrier -> Result)
    (compatible : ProjectionCompatible Q.project map) (x : Carrier) :
    Q.descend map compatible (Q.project x) = map x :=
  Q.universal.descend_project map compatible x

/-- A factor through the quotient is uniquely determined by its values after
the canonical projection. -/
theorem descend_unique (Q : LedgerQuotient.{uCarrier, uQuotient} L)
    {Result : Type (max uCarrier uQuotient)} (map : Carrier -> Result)
    (compatible : ProjectionCompatible Q.project map)
    (candidate : Q.Quotient -> Result)
    (commutes : forall x, candidate (Q.project x) = map x)
    (q : Q.Quotient) : candidate q = Q.descend map compatible q :=
  Q.universal.descend_unique map compatible candidate commutes q

end LedgerQuotient

/-- Evidence that a later invariant can be computed entirely on the reduced
carrier represented by a ledger quotient. -/
structure LaterInvariantDescends
    {Carrier : Type uCarrier} {C : ClosureOperator Carrier}
    {TargetNull : Carrier -> Prop} {L : ClosedClassLedger C TargetNull}
    (Q : LedgerQuotient.{uCarrier, uQuotient} L)
    (Value : Type (max uCarrier uQuotient))
    (invariant : Carrier -> Value) : Prop where
  compatible : ProjectionCompatible Q.project invariant

namespace LaterInvariantDescends

variable {Carrier : Type uCarrier} {C : ClosureOperator Carrier}
  {TargetNull : Carrier -> Prop} {L : ClosedClassLedger C TargetNull}
  {Q : LedgerQuotient.{uCarrier, uQuotient} L}
  {Value : Type (max uCarrier uQuotient)} {invariant : Carrier -> Value}

/-- The invariant induced on the quotient by its descent certificate. -/
def factor (D : LaterInvariantDescends Q Value invariant) :
    Q.Quotient -> Value :=
  Q.descend invariant D.compatible

@[simp] theorem factor_project
    (D : LaterInvariantDescends Q Value invariant) (x : Carrier) :
    D.factor (Q.project x) = invariant x :=
  Q.descend_project invariant D.compatible x

/-- Any other quotient-level realization of the invariant is the canonical
factor. -/
theorem factor_unique (D : LaterInvariantDescends Q Value invariant)
    (candidate : Q.Quotient -> Value)
    (commutes : forall x, candidate (Q.project x) = invariant x)
    (q : Q.Quotient) : candidate q = D.factor q :=
  Q.descend_unique invariant D.compatible candidate commutes q

end LaterInvariantDescends

end Hypostructure.Core
