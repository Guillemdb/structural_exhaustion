import Hypostructure.Core.Prelude

/-!
# Closed-class ledgers

This module separates mathematical classes that have already been proved
target-null from the proof ledger attached to a residual.  The closure model
is supplied by a domain; Core only records and extends closed sets.
-/

namespace Hypostructure.Core

universe u

/-- A domain-neutral closure operation on sets of carrier objects. -/
structure ClosureOperator (Carrier : Type u) where
  close : Set Carrier -> Set Carrier
  extensive : forall S, Set.Subset S (close S)
  monotone : forall {S T}, Set.Subset S T -> Set.Subset (close S) (close T)
  idempotent : forall S, close (close S) = close S

namespace ClosureOperator

variable {Carrier : Type u}

/-- A set is closed when applying the registered closure does not enlarge it. -/
def IsClosed (C : ClosureOperator Carrier) (S : Set Carrier) : Prop :=
  C.close S = S

/-- Closing any set produces a closed set. -/
theorem close_isClosed (C : ClosureOperator Carrier) (S : Set Carrier) :
    C.IsClosed (C.close S) :=
  C.idempotent S

/-- The identity closure, useful for discrete or already-closed carriers. -/
def identity (Carrier : Type u) : ClosureOperator Carrier where
  close := id
  extensive := fun _ => Set.Subset.rfl
  monotone := fun subset => subset
  idempotent := fun _ => rfl

@[simp] theorem identity_close (S : Set Carrier) :
    (identity Carrier).close S = S :=
  rfl

end ClosureOperator

/-- A predicate is stable under a domain's closure operation.  This is the
extra semantic fact needed to close a union of target-null generators. -/
structure ClosureStable {Carrier : Type u} (C : ClosureOperator Carrier)
    (Predicate : Carrier -> Prop) : Prop where
  preserves : forall {S : Set Carrier},
    (forall {x}, x ∈ S -> Predicate x) ->
      forall {x}, x ∈ C.close S -> Predicate x

namespace ClosureStable

variable {Carrier : Type u} {Predicate : Carrier -> Prop}

/-- Every predicate is stable under identity closure. -/
def identity : ClosureStable (ClosureOperator.identity Carrier) Predicate where
  preserves := by
    intro S preserved x hx
    exact preserved hx

end ClosureStable

/-- A closure-stable family whose members have already been proved target-null. -/
structure ClosedClassLedger {Carrier : Type u} (C : ClosureOperator Carrier)
    (TargetNull : Carrier -> Prop) where
  classes : Set Carrier
  closed : C.close classes = classes
  targetNull : forall {x}, x ∈ classes -> TargetNull x

namespace ClosedClassLedger

variable {Carrier : Type u} {C : ClosureOperator Carrier}
  {TargetNull : Carrier -> Prop}

/-- Close a supplied generator family once its entire closure is certified
target-null. -/
def generated (generators : Set Carrier)
    (targetNull : forall {x}, x ∈ C.close generators -> TargetNull x) :
    ClosedClassLedger C TargetNull where
  classes := C.close generators
  closed := C.idempotent generators
  targetNull := targetNull

/-- Extend a ledger by new target-null generators.  Closure stability is the
precise justification for including limit, span, or equivalence consequences
without proving them one at a time. -/
def extend (L : ClosedClassLedger C TargetNull)
    (stable : ClosureStable C TargetNull) (added : Set Carrier)
    (addedTargetNull : forall {x}, x ∈ added -> TargetNull x) :
    ClosedClassLedger C TargetNull :=
  generated (L.classes ∪ added) (by
    intro x hx
    exact stable.preserves (by
      intro y hy
      rcases hy with hy | hy
      · exact L.targetNull hy
      · exact addedTargetNull hy) hx)

/-- Existing classes embed in a justified extension. -/
theorem subset_extend (L : ClosedClassLedger C TargetNull)
    (stable : ClosureStable C TargetNull) (added : Set Carrier)
    (addedTargetNull : forall {x}, x ∈ added -> TargetNull x) :
    Set.Subset L.classes (L.extend stable added addedTargetNull).classes := by
  intro x hx
  change x ∈ C.close (L.classes ∪ added)
  exact C.extensive _ (Or.inl hx)

/-- Every newly supplied generator embeds in the resulting closed ledger. -/
theorem added_subset_extend (L : ClosedClassLedger C TargetNull)
    (stable : ClosureStable C TargetNull) (added : Set Carrier)
    (addedTargetNull : forall {x}, x ∈ added -> TargetNull x) :
    Set.Subset added (L.extend stable added addedTargetNull).classes := by
  intro x hx
  change x ∈ C.close (L.classes ∪ added)
  exact C.extensive _ (Or.inr hx)

/-- The closed union of two ledgers, available when target-nullity is stable
under the registered closure. -/
def union (left right : ClosedClassLedger C TargetNull)
    (stable : ClosureStable C TargetNull) : ClosedClassLedger C TargetNull :=
  left.extend stable right.classes (fun hx => right.targetNull hx)

/-- The left ledger embeds in a justified closed union. -/
theorem subset_union_left (left right : ClosedClassLedger C TargetNull)
    (stable : ClosureStable C TargetNull) :
    Set.Subset left.classes (left.union right stable).classes :=
  left.subset_extend stable right.classes (fun hx => right.targetNull hx)

/-- The right ledger embeds in a justified closed union. -/
theorem subset_union_right (left right : ClosedClassLedger C TargetNull)
    (stable : ClosureStable C TargetNull) :
    Set.Subset right.classes (left.union right stable).classes :=
  left.added_subset_extend stable right.classes (fun hx => right.targetNull hx)

end ClosedClassLedger

end Hypostructure.Core
