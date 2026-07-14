import StructuralExhaustion.CT14.Automation
import StructuralExhaustion.Core.EnumerationCombinators
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace StructuralExhaustion.Graph.CertificateClosedFanCharge

open StructuralExhaustion

universe uAmbient uBranch uMember

/-!
# CT14 certificate-closed fan charge

This profile scans an exact finite fan-member universe and classifies every
member by one decidable `Closed` predicate. CT14 records the closed/open
multiplicities, and the graph layer proves the exact quarter-charge identity

`(11 - 4k) - c + 3(k-c) = 11 - k - 4c`.

Thus the certificate-closed condition `4c + k ≤ 11` makes the complete
closed-neighbourhood charge nonnegative. No subset or label assignment is
enumerated.
-/

structure Profile (Member : Type uMember) where
  members : FinEnum Member
  Closed : Member → Prop
  closedDecidable : ∀ member, Decidable (Closed member)
  quarterCharge : Member → Int
  closedQuarterCharge : ∀ member, Closed member → quarterCharge member = -1
  openQuarterChargeLower : ∀ member, ¬Closed member → 3 ≤ quarterCharge member

namespace Profile

variable {Member : Type uMember} (profile : Profile Member)

def closedMass (member : Member) : Nat :=
  @ite Nat (profile.Closed member) (profile.closedDecidable member) 1 0

@[implicit_reducible]
def closedMembers : FinEnum {member : Member // profile.Closed member} :=
  Core.Enumeration.subtype profile.members profile.Closed
    profile.closedDecidable

def capability (problem : Core.Problem.{uAmbient, uBranch}) :
    CT14.Capability problem where
  Member := Member
  members := profile.members
  Label := Unit
  labelDecidableEq := inferInstance
  memberLowerMass := fun _context member => profile.closedMass member
  memberCapacity := fun _context _member => some 1
  memberLabel := fun _context _member => some ()

def input {problem : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext problem) :
    CT14.Input (profile.capability problem) context :=
  ⟨⟩

def closedCount {problem : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext problem) : Nat :=
  CT14.lowerMass (profile.capability problem) context

theorem closedCount_eq_closedMembers_card
    {problem : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext problem) :
    profile.closedCount context = profile.closedMembers.card := by
  letI : DecidablePred profile.Closed := profile.closedDecidable
  letI : FinEnum Member := profile.members
  letI : FinEnum {member : Member // profile.Closed member} :=
    profile.closedMembers
  rw [FinEnum.card_eq_fintypeCard, Fintype.card_subtype]
  unfold closedCount CT14.lowerMass capability
  let collection := profile.members.toOrderedCollection
  change (collection.values.map profile.closedMass).sum =
    ((Finset.univ.filter profile.Closed).card : Nat)
  rw [Core.OrderedCollection.sum_values_eq_sum_toFinset]
  have allMembers : collection.toFinset = Finset.univ := by
    ext member
    simp only [Finset.mem_univ, iff_true]
    change member ∈ collection.values.toFinset
    rw [List.mem_toFinset]
    exact profile.members.mem_orderedValues member
  rw [allMembers]
  simpa [closedMass] using
    (Finset.sum_boole (R := Nat) profile.Closed
      (Finset.univ : Finset Member))

def openCount {problem : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext problem) : Nat :=
  profile.members.card - profile.closedCount context

theorem lowerMass_eq_closedCount
    {problem : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext problem) :
    CT14.lowerMass (profile.capability problem) context =
      profile.closedCount context :=
  rfl

theorem closedCount_le_card
    {problem : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext problem) :
    profile.closedCount context ≤ profile.members.card := by
  have listBound : ∀ values : List Member,
      (values.map profile.closedMass).sum ≤ values.length := by
    intro values
    induction values with
    | nil => simp
    | cons member tail ih =>
        by_cases closed : profile.Closed member
        · simp [closedMass, closed]
          omega
        · simp [closedMass, closed]
          omega
  unfold closedCount CT14.lowerMass
  change (profile.members.orderedValues.map profile.closedMass).sum ≤
    profile.members.card
  rw [← FinEnum.orderedValues_length]
  exact listBound profile.members.orderedValues

theorem upperCapacity_eq_card
    {problem : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext problem) :
    CT14.upperCapacity (profile.capability problem) context =
      profile.members.card := by
  unfold CT14.upperCapacity
  change (profile.members.orderedValues.map (fun _member => 1)).sum =
    profile.members.card
  have sumOnes : ∀ values : List Member,
      (values.map (fun _member => 1)).sum = values.length := by
    intro values
    induction values with
    | nil => rfl
    | cons _ tail ih =>
        simp only [List.map_cons, List.sum_cons, List.length_cons, ih]
        omega
  rw [sumOnes, FinEnum.orderedValues_length]

theorem count_partition
    {problem : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext problem) :
    profile.closedCount context + profile.openCount context =
      profile.members.card := by
  unfold openCount
  have bound := profile.closedCount_le_card context
  omega

theorem lowerMass_le_upperCapacity
    {problem : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext problem) :
    CT14.lowerMass (profile.capability problem) context ≤
      CT14.upperCapacity (profile.capability problem) context := by
  rw [profile.lowerMass_eq_closedCount context,
    profile.upperCapacity_eq_card context]
  have partition := profile.count_partition context
  omega

def run {problem : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext problem) :
    CT14.ExecutionResult (profile.capability problem) context :=
  CT14.run (profile.capability problem) context (profile.input context)

theorem run_terminal
    {problem : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext problem) :
    (profile.run context).terminal = .capacity :=
  CT14.run_terminal_capacity_of_complete
    (profile.capability problem) context (profile.input context)
    (fun _member => ⟨1, rfl⟩)
    (fun _member => ⟨(), rfl⟩)
    (profile.lowerMass_le_upperCapacity context)

theorem run_trace
    {problem : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext problem) :
    (profile.run context).trace =
      [.entry, .lowerMass, .memberScan, .upperCapacity, .comparison,
        .capacityTerminal] :=
  CT14.run_trace_capacity_of_complete
    (profile.capability problem) context (profile.input context)
    (fun _member => ⟨1, rfl⟩)
    (fun _member => ⟨(), rfl⟩)
    (profile.lowerMass_le_upperCapacity context)

/-- Lower bound for the augmented closed-neighbourhood charge, in quarter
units. The centre contributes `11-4k`, every closed member contributes `-1`,
and every open member contributes `3`. -/
def neighborhoodQuarterChargeLower
    {problem : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext problem) : Int :=
  11 - 4 * (profile.members.card : Int) -
    (profile.closedCount context : Int) +
      3 * (profile.openCount context : Int)

theorem neighborhoodQuarterChargeLower_eq
    {problem : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext problem) :
    profile.neighborhoodQuarterChargeLower context =
      11 - (profile.members.card : Int) -
        4 * (profile.closedCount context : Int) := by
  have partition := profile.count_partition context
  have partitionInt :
      (profile.closedCount context : Int) +
          (profile.openCount context : Int) = profile.members.card := by
    exact_mod_cast partition
  unfold neighborhoodQuarterChargeLower
  omega

/-- The certificate-closed deficit condition is exactly the nonnegativity of
the computed neighborhood charge lower bound. -/
theorem neighborhoodQuarterChargeLower_nonnegative
    {problem : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext problem)
    (certificateClosed :
      4 * profile.closedCount context + profile.members.card ≤ 11) :
    0 ≤ profile.neighborhoodQuarterChargeLower context := by
  rw [profile.neighborhoodQuarterChargeLower_eq context]
  have closedInt :
      4 * (profile.closedCount context : Int) +
        (profile.members.card : Int) ≤ 11 := by
    exact_mod_cast certificateClosed
  omega

structure VerifiedStage
    {problem : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext problem) : Prop where
  terminal : (profile.run context).terminal = .capacity
  trace : (profile.run context).trace =
    [.entry, .lowerMass, .memberScan, .upperCapacity, .comparison,
      .capacityTerminal]
  lowerExact : CT14.lowerMass (profile.capability problem) context =
    profile.closedCount context
  partition : profile.closedCount context + profile.openCount context =
    profile.members.card
  chargeExact : profile.neighborhoodQuarterChargeLower context =
    11 - (profile.members.card : Int) -
      4 * (profile.closedCount context : Int)

def verifiedStage
    {problem : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext problem) :
    profile.VerifiedStage context where
  terminal := profile.run_terminal context
  trace := profile.run_trace context
  lowerExact := profile.lowerMass_eq_closedCount context
  partition := profile.count_partition context
  chargeExact := profile.neighborhoodQuarterChargeLower_eq context

end Profile

end StructuralExhaustion.Graph.CertificateClosedFanCharge
