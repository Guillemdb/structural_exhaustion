import Hypostructure.CT14.Capability
import Hypostructure.Core.Finite.Accounting

/-!
# CT14 generated states and ledgers

All data in this file is computed from the exact predecessor schedule.  The
constructors of generated ledgers are private; callers consume the canonical
builders and their retained exactness proofs.
-/

namespace Hypostructure.CT14

universe uPrevious uMember uLabel

variable {Previous : Type uPrevious}
  {spec : Spec.{uPrevious, uMember, uLabel} Previous}

/-- Ordered lower-mass entries on the residual-owned member family. -/
def lowerMassEntries (capability : Capability spec) (previous : Previous) :
    List (spec.Member previous × Nat) :=
  (capability.membersAt previous).values.map fun member =>
    (member, spec.memberLowerMass previous member)

/-- Exact aggregate lower mass. -/
def lowerMass (capability : Capability spec) (previous : Previous) : Nat :=
  (lowerMassEntries capability previous).map Prod.snd |>.sum

/-- Framework-generated lower-mass ledger. -/
structure LowerMassLedger (capability : Capability spec)
    (previous : Previous) where
  private mk ::
  entries : List (spec.Member previous × Nat)
  entries_exact : entries = lowerMassEntries capability previous
  total : Nat
  total_exact : total = lowerMass capability previous

/-- Compute the canonical lower-mass ledger. -/
def computeLowerMass (capability : Capability spec) (previous : Previous) :
    LowerMassLedger capability previous :=
  .mk (lowerMassEntries capability previous) rfl
    (lowerMass capability previous) rfl

/-- First member without a finite upper capacity, in exact schedule order. -/
abbrev UnboundedMemberResidual (capability : Capability spec)
    (previous : Previous) :=
  Core.Finite.Search.IndexedHit (capability.membersAt previous)
    (fun member => spec.memberCapacity previous member = none)

/-- Exhaustive absence of an unbounded member on the exact schedule. -/
abbrev CapacityComplete (capability : Capability spec)
    (previous : Previous) :=
  Core.Finite.Search.Avoids (capability.membersAt previous)
    (fun member => spec.memberCapacity previous member = none)

/-- First member without a label, in exact schedule order. -/
abbrev MissingLabelResidual (capability : Capability spec)
    (previous : Previous) :=
  Core.Finite.Search.IndexedHit (capability.membersAt previous)
    (fun member => spec.memberLabel previous member = none)

/-- Exhaustive absence of a missing label on the exact schedule. -/
abbrev LabelComplete (capability : Capability spec)
    (previous : Previous) :=
  Core.Finite.Search.Avoids (capability.membersAt previous)
    (fun member => spec.memberLabel previous member = none)

/-- Ordered capacity entries.  The completeness certificate retained by the
generated ledger proves every `getD` reads an actual finite capacity. -/
def capacityEntries (capability : Capability spec) (previous : Previous) :
    List (spec.Member previous × Nat) :=
  (capability.membersAt previous).values.map fun member =>
    (member, (spec.memberCapacity previous member).getD 0)

/-- Exact aggregate finite capacity on the supplied member family. -/
def upperCapacity (capability : Capability spec) (previous : Previous) : Nat :=
  (capacityEntries capability previous).map Prod.snd |>.sum

/-- Exact multiplicity of one label, without enumerating the label type. -/
def multiplicity (capability : Capability spec) (previous : Previous)
    (label : spec.Label previous) : Nat :=
  Core.Finite.Accounting.fibreCount (capability.membersAt previous)
    (spec.memberLabel previous) (some label) (by
      letI : DecidableEq (spec.Label previous) :=
        capability.labelDecidableEq previous
      exact inferInstance)

/-- Canonical finite-capacity ledger. -/
structure CapacityLedger (capability : Capability spec)
    (previous : Previous) where
  private mk ::
  entries : List (spec.Member previous × Nat)
  entries_exact : entries = capacityEntries capability previous
  total : Nat
  total_exact : total = upperCapacity capability previous
  complete : CapacityComplete capability previous

/-- Canonical label-multiplicity ledger.  It is a finite-member fold exposed
as a function on labels; the framework never enumerates label assignments. -/
structure MultiplicityLedger (capability : Capability spec)
    (previous : Previous) where
  private mk ::
  counts : spec.Label previous -> Nat
  counts_exact : forall label,
    counts label = multiplicity capability previous label
  complete : LabelComplete capability previous

/-- Complete CT14 aggregate ledger generated after both optional-data scans. -/
structure AggregateLedger (capability : Capability spec)
    (previous : Previous) where
  private mk ::
  lower : LowerMassLedger capability previous
  capacity : CapacityLedger capability previous
  multiplicity : MultiplicityLedger capability previous

/-- Build the unique capacity and multiplicity ledgers from exhaustive scans. -/
def buildAggregateLedger (capability : Capability spec) (previous : Previous)
    (lower : LowerMassLedger capability previous)
    (bounded : CapacityComplete capability previous)
    (labeled : LabelComplete capability previous) :
    AggregateLedger capability previous :=
  .mk lower
    (.mk (capacityEntries capability previous) rfl
      (upperCapacity capability previous) rfl bounded)
    (.mk (multiplicity capability previous) (fun _label => rfl) labeled)

/-- Aggregate overload certificate generated by the final comparison. -/
abbrev AggregateCertificate (capability : Capability spec)
    (previous : Previous) (ledger : AggregateLedger capability previous) : Prop :=
  ledger.capacity.total < ledger.lower.total

/-- Capacity residual generated by the complementary final comparison. -/
abbrev CapacityResidual (capability : Capability spec)
    (previous : Previous) (ledger : AggregateLedger capability previous) : Prop :=
  ledger.lower.total <= ledger.capacity.total

end Hypostructure.CT14
