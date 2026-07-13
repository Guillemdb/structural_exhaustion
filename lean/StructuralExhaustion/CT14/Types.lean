import StructuralExhaustion.Core.AutomationFirst

namespace StructuralExhaustion.CT14

universe uMember uLabel

structure Capability (P : Core.Problem) where
  Member : Type uMember
  members : FinEnum Member
  Label : Type uLabel
  labelDecidableEq : DecidableEq Label
  memberLowerMass : Core.BranchContext P → Member → Nat
  memberCapacity : Core.BranchContext P → Member → Option Nat
  memberLabel : Core.BranchContext P → Member → Option Label

structure Input {P : Core.Problem} (_C : Capability P)
    (_ctx : Core.BranchContext P) where
namespace Capability
def tacticInterface {P : Core.Problem} (C : Capability P) :
    Core.Routing.TacticInterface where
  Context := Core.BranchContext P
  Trigger := Input C
end Capability

def lowerMass {P : Core.Problem} (C : Capability P)
    (ctx : Core.BranchContext P) : Nat :=
  (C.members.orderedValues.map (C.memberLowerMass ctx)).sum

structure LowerMassState {P : Core.Problem} (C : Capability P)
    (ctx : Core.BranchContext P) where
  value : Nat
  exact : value = lowerMass C ctx

structure UnboundedMemberResidual {P : Core.Problem} (C : Capability P)
    (ctx : Core.BranchContext P) where
  member : C.Member
  missing : C.memberCapacity ctx member = none

structure MissingLabelResidual {P : Core.Problem} (C : Capability P)
    (ctx : Core.BranchContext P) where
  member : C.Member
  missing : C.memberLabel ctx member = none

def upperCapacity {P : Core.Problem} (C : Capability P)
    (ctx : Core.BranchContext P) : Nat :=
  (C.members.orderedValues.map fun m => (C.memberCapacity ctx m).getD 0).sum

def multiplicity {P : Core.Problem} (C : Capability P)
    (ctx : Core.BranchContext P) (label : C.Label) : Nat :=
  C.members.orderedValues.foldl (fun count member =>
    match C.memberLabel ctx member with
    | some found =>
        match C.labelDecidableEq found label with
        | .isTrue _ => count + 1
        | .isFalse _ => count
    | none => count) 0

structure MemberScanState {P : Core.Problem} (C : Capability P)
    (ctx : Core.BranchContext P) where
  lower : LowerMassState C ctx
  bounded : ∀ member, ∃ value, C.memberCapacity ctx member = some value
  labeled : ∀ member, ∃ label, C.memberLabel ctx member = some label

structure LedgerState {P : Core.Problem} (C : Capability P)
    (ctx : Core.BranchContext P) where
  scan : MemberScanState C ctx
  upper : Nat
  upperExact : upper = upperCapacity C ctx
  counts : C.Label → Nat
  countsExact : ∀ label, counts label = multiplicity C ctx label

inductive ScanDecision {P : Core.Problem} (C : Capability P)
    (ctx : Core.BranchContext P) where
  | unbounded (r : UnboundedMemberResidual C ctx)
  | missingLabel (r : MissingLabelResidual C ctx)
  | complete (s : MemberScanState C ctx)

private def noneDecidable {α : Type u} (value : Option α) :
    Decidable (value = none) :=
  match value with
  | none => .isTrue rfl
  | some _ => .isFalse (by intro h; cases h)

def scanMembers {P : Core.Problem} (C : Capability P)
    (ctx : Core.BranchContext P) (lower : LowerMassState C ctx) :
    ScanDecision C ctx :=
  match Core.FiniteSearch.first C.members
      (fun m => C.memberCapacity ctx m = none)
      (fun m => noneDecidable (C.memberCapacity ctx m)) with
  | .found hit => .unbounded ⟨hit.value, hit.holds⟩
  | .absent capacityPresent =>
      match Core.FiniteSearch.first C.members
          (fun m => C.memberLabel ctx m = none)
          (fun m => noneDecidable (C.memberLabel ctx m)) with
      | .found hit => .missingLabel ⟨hit.value, hit.holds⟩
      | .absent labelPresent => .complete {
          lower := lower
          bounded := fun member => by
            cases h : C.memberCapacity ctx member with
            | none => exact (capacityPresent member
                (C.members.mem_orderedValues member) h).elim
            | some value => exact ⟨value, rfl⟩
          labeled := fun member => by
            cases h : C.memberLabel ctx member with
            | none => exact (labelPresent member
                (C.members.mem_orderedValues member) h).elim
            | some label => exact ⟨label, rfl⟩
        }

def computeLedger {P : Core.Problem} (C : Capability P)
    (ctx : Core.BranchContext P) (scan : MemberScanState C ctx) :
    LedgerState C ctx where
  scan := scan
  upper := upperCapacity C ctx
  upperExact := rfl
  counts := multiplicity C ctx
  countsExact := fun _ => rfl

structure AggregateCertificate {P : Core.Problem} (C : Capability P)
    (ctx : Core.BranchContext P) where
  lower : Nat
  upper : Nat
  lowerExact : lower = lowerMass C ctx
  upperExact : upper = upperCapacity C ctx
  exceeds : upper < lower

structure CapacityResidual {P : Core.Problem} (C : Capability P)
    (ctx : Core.BranchContext P) where
  lower : Nat
  upper : Nat
  lowerExact : lower = lowerMass C ctx
  upperExact : upper = upperCapacity C ctx
  within : lower ≤ upper

inductive ComparisonDecision {P : Core.Problem} (C : Capability P)
    (ctx : Core.BranchContext P) where
  | exceeds (c : AggregateCertificate C ctx)
  | within (r : CapacityResidual C ctx)

def compare {P : Core.Problem} (C : Capability P) (ctx : Core.BranchContext P)
    (ledger : LedgerState C ctx) :
    ComparisonDecision C ctx :=
  if h : ledger.upper < ledger.scan.lower.value then
    .exceeds ⟨ledger.scan.lower.value, ledger.upper,
      ledger.scan.lower.exact, ledger.upperExact, h⟩
  else .within ⟨ledger.scan.lower.value, ledger.upper,
    ledger.scan.lower.exact, ledger.upperExact,
    Nat.le_of_not_gt h⟩

end StructuralExhaustion.CT14
