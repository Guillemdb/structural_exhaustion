import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import StructuralExhaustion.Core.FiniteWeightedSelection
import StructuralExhaustion.Graph.CertificateClosedFanCharge

namespace StructuralExhaustion.Graph.CertificateClosedFanCandidate

open StructuralExhaustion
open scoped BigOperators

universe uAmbient uBranch uMember uVertex

/-!
# Concrete certificate-closed fan candidates

The item universe is the exact fan-member enumeration already scanned by
CT14.  A selected member contributes its exact assigned-incidence quarter
charge; the earlier CT14 theorem proves that a closed member has charge `-1`
and an open member has charge at least `3`.  The required weight is the
negation of the center contribution `11 - 4k`.  Thus candidate validity is
definitionally the certificate-closed paying inequality.  The framework never
evaluates the powerset of fan members.
-/

/-- Ordinary-reserve occupancy of literal vertex carriers. -/
structure VertexReserve (Vertex : Type uVertex) where
  Used : Vertex → Prop
  usedDecidable : ∀ vertex, Decidable (Used vertex)

variable {Member : Type uMember} {Vertex : Type uVertex}

namespace Profile

variable
  (chargeProfile : CertificateClosedFanCharge.Profile Member)
  (vertexDecidableEq : DecidableEq Vertex)
  (center : Vertex)
  (vertex : Member → Vertex)
  (reserve : VertexReserve Vertex)

/-- Coarse CT14 lower contribution used in the certificate arithmetic. -/
def memberLowerQuarterCharge (member : Member) : Int :=
  @ite Int (chargeProfile.Closed member) (chargeProfile.closedDecidable member)
    (-1) 3

/-- Exact center charge in quarter units. -/
def centerQuarterCharge : Int :=
  11 - 4 * (chargeProfile.members.card : Int)

/-- The literal finite candidate profile for the certificate-closed branch. -/
def selectionProfile : Core.FiniteWeightedSelection.Profile Member Vertex where
  items := chargeProfile.members
  carrierDecidableEq := vertexDecidableEq
  mandatory := fun _member => False
  mandatoryDecidable := fun _member => inferInstance
  forbidden := fun member => reserve.Used (vertex member)
  forbiddenDecidable := fun member => reserve.usedDecidable (vertex member)
  weight := chargeProfile.quarterCharge
  required := -centerQuarterCharge chargeProfile
  baseSupport := {center}
  itemSupport := fun member => {vertex member}

abbrev Candidate :=
  (selectionProfile chargeProfile vertexDecidableEq center vertex reserve).Candidate

/-- The complete member list has exactly the coarse closed/open CT14 lower
charge. -/
theorem allItems_lowerWeight_eq
    {problem : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext problem) :
    (∑ member ∈ (selectionProfile chargeProfile vertexDecidableEq center
        vertex reserve).allItems,
      memberLowerQuarterCharge chargeProfile member) =
        -(chargeProfile.closedCount context : Int) +
          3 * (chargeProfile.openCount context : Int) := by
  let collection := chargeProfile.members.toOrderedCollection
  have listFormula : ∀ values : List Member,
      (values.map (memberLowerQuarterCharge chargeProfile)).sum =
        3 * (values.length : Int) -
          4 * ((values.map chargeProfile.closedMass).sum : Int) := by
    intro values
    induction values with
    | nil => simp
    | cons member tail ih =>
        by_cases closed : chargeProfile.Closed member
        · simp [memberLowerQuarterCharge, CertificateClosedFanCharge.Profile.closedMass,
            closed, ih]
          omega
        · simp [memberLowerQuarterCharge, CertificateClosedFanCharge.Profile.closedMass,
            closed, ih]
          omega
  have orderedSum :
      (chargeProfile.members.orderedValues.map
        (memberLowerQuarterCharge chargeProfile)).sum =
      ∑ member ∈ (selectionProfile chargeProfile vertexDecidableEq center
        vertex reserve).allItems,
        memberLowerQuarterCharge chargeProfile member := by
    change (collection.values.map (memberLowerQuarterCharge chargeProfile)).sum = _
    rw [Core.OrderedCollection.sum_values_eq_sum_toFinset]
    rfl
  rw [← orderedSum, listFormula]
  have partition := chargeProfile.count_partition context
  have closedFormula : chargeProfile.closedCount context =
      (chargeProfile.members.orderedValues.map chargeProfile.closedMass).sum := rfl
  have cardFormula : chargeProfile.members.card =
      chargeProfile.members.orderedValues.length := by
    exact (FinEnum.orderedValues_length chargeProfile.members).symm
  rw [closedFormula, cardFormula] at partition
  have partitionInt :
      ((chargeProfile.members.orderedValues.map
          chargeProfile.closedMass).sum : Int) +
        (chargeProfile.openCount context : Int) =
          (chargeProfile.members.orderedValues.length : Int) := by
    exact_mod_cast partition
  omega

theorem memberLowerQuarterCharge_le (member : Member) :
    memberLowerQuarterCharge chargeProfile member ≤
      chargeProfile.quarterCharge member := by
  by_cases closed : chargeProfile.Closed member
  · rw [chargeProfile.closedQuarterCharge member closed]
    simp [memberLowerQuarterCharge, closed]
  · have lower := chargeProfile.openQuarterChargeLower member closed
    simpa [memberLowerQuarterCharge, closed] using lower

/-- The exact assigned-degree charge of the complete member list dominates
the CT14 closed/open lower bound. -/
theorem allItems_weight_ge
    {problem : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext problem) :
    -(chargeProfile.closedCount context : Int) +
        3 * (chargeProfile.openCount context : Int) ≤
      ∑ member ∈ (selectionProfile chargeProfile vertexDecidableEq center
        vertex reserve).allItems, chargeProfile.quarterCharge member := by
  rw [← allItems_lowerWeight_eq chargeProfile vertexDecidableEq center vertex
    reserve context]
  exact Finset.sum_le_sum fun member _member =>
    memberLowerQuarterCharge_le chargeProfile member

/-- Candidate validity is exactly nonnegative selected center-plus-member
quarter charge. -/
theorem Candidate.charge_nonnegative (candidate :
    Candidate chargeProfile vertexDecidableEq center vertex reserve) :
    0 ≤ centerQuarterCharge chargeProfile +
      ∑ member ∈ candidate.1, chargeProfile.quarterCharge member := by
  have payment := (selectionProfile chargeProfile vertexDecidableEq center
    vertex reserve).payment candidate
  change -centerQuarterCharge chargeProfile ≤
    ∑ member ∈ candidate.1, chargeProfile.quarterCharge member at payment
  omega

theorem Candidate.selected_reserve_free (candidate :
    Candidate chargeProfile vertexDecidableEq center vertex reserve)
    {member : Member} (selected : member ∈ candidate.1) :
    ¬reserve.Used (vertex member) :=
  Core.FiniteWeightedSelection.Profile.selected_not_forbidden
    (selectionProfile chargeProfile vertexDecidableEq center vertex reserve)
    candidate selected

theorem Candidate.center_mem_support (candidate :
    Candidate chargeProfile vertexDecidableEq center vertex reserve) :
    center ∈ (selectionProfile chargeProfile vertexDecidableEq center vertex
      reserve).carrierSupport candidate := by
  have centerBase : center ∈
      (selectionProfile chargeProfile vertexDecidableEq center vertex reserve).baseSupport := by
    change center ∈ ({center} : Finset Vertex)
    simp
  exact Core.FiniteWeightedSelection.Profile.baseSupport_subset
    (selectionProfile chargeProfile vertexDecidableEq center vertex reserve)
    candidate centerBase

theorem Candidate.selected_vertex_mem_support (candidate :
    Candidate chargeProfile vertexDecidableEq center vertex reserve)
    {member : Member} (selected : member ∈ candidate.1) :
    vertex member ∈ (selectionProfile chargeProfile vertexDecidableEq center
      vertex reserve).carrierSupport candidate := by
  have vertexItem : vertex member ∈
      (selectionProfile chargeProfile vertexDecidableEq center vertex reserve).itemSupport
        member := by
    change vertex member ∈ ({vertex member} : Finset Vertex)
    simp
  exact Core.FiniteWeightedSelection.Profile.itemSupport_subset
    (selectionProfile chargeProfile vertexDecidableEq center vertex reserve)
    candidate selected vertexItem

/-- The complete declared carrier universe of a certificate-closed fan is
ambiently reachable from its center whenever its literal member map consists
of actual neighbors. -/
theorem declaredCarrierSupport_reachable
    {G : SimpleGraph Vertex}
    (adjacent : ∀ member, G.Adj center (vertex member))
    {carrier : Vertex}
    (member : carrier ∈
      (selectionProfile chargeProfile vertexDecidableEq center vertex
        reserve).declaredCarrierSupport) :
    G.Reachable center carrier := by
  apply Core.FiniteWeightedSelection.Profile.declaredCarrierSupport_induction
    (selectionProfile chargeProfile vertexDecidableEq center vertex reserve)
    (fun carrier => G.Reachable center carrier) ?_ ?_ member
  · intro baseCarrier baseMember
    have equal : baseCarrier = center := by
      simpa [selectionProfile] using baseMember
    subst baseCarrier
    exact SimpleGraph.Reachable.rfl
  · intro selected itemCarrier itemMember
    have equal : itemCarrier = vertex selected := by
      simpa [selectionProfile] using itemMember
    subst itemCarrier
    exact (adjacent selected).reachable

/-- The already verified certificate-closed charge constructs the complete
fan-neighbour candidate whenever none of its vertex carriers is reserved. -/
noncomputable def allItemsCandidate
    {problem : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext problem)
    (chargeNonnegative :
      0 ≤ chargeProfile.neighborhoodQuarterChargeLower context)
    (reserveFree : ∀ member, ¬reserve.Used (vertex member)) :
    Candidate chargeProfile vertexDecidableEq center vertex reserve := by
  apply Core.FiniteWeightedSelection.Profile.allItemsCandidate
    (selectionProfile chargeProfile vertexDecidableEq center vertex reserve)
    reserveFree
  change -centerQuarterCharge chargeProfile ≤
    ∑ member ∈ (selectionProfile chargeProfile vertexDecidableEq center
      vertex reserve).allItems, chargeProfile.quarterCharge member
  have exactDominates := allItems_weight_ge chargeProfile vertexDecidableEq center
    vertex reserve context
  unfold centerQuarterCharge
  unfold CertificateClosedFanCharge.Profile.neighborhoodQuarterChargeLower at chargeNonnegative
  omega

end Profile

end StructuralExhaustion.Graph.CertificateClosedFanCandidate
