import Mathlib.Tactic
import StructuralExhaustion.Graph.FiniteObject

namespace StructuralExhaustion.Graph.AssignedSupportCharge

open StructuralExhaustion
open scoped BigOperators

universe u

/-!
# Exact quarter-unit charge of an assigned graph support

This module owns the algebra behind the manuscript's Type B ledger.  A
profile consists only of literal graph data: a counted vertex set and a set
of vertices whose ambient surplus is assigned to it.  Internal degree,
positive deficiency, ambient surplus, net charge, and the augmented center
ledger are definitions.  In particular the B-ledger identity is a theorem,
not a certificate field.

All quantities are kept in quarter units, so no rational normalization or
rounding enters the formal statement.  The definitions are proof-facing and
are not installed in an executable CT runner.
-/

variable {V : Type u}

structure Profile (object : FiniteObject V) where
  /-- Vertices counted by the support's deficiency and size. -/
  core : Finset V
  /-- Ambient high-center occurrences whose surplus is assigned here. -/
  assignedCenters : Finset V

namespace Profile

variable {object : FiniteObject V} (profile : Profile object)

/-- Degree inside the literal induced core. -/
def internalDegree (vertex : V) : Nat := by
  letI : FinEnum V := object.input.vertices
  letI : DecidableEq V := object.input.vertices.decEq
  letI : DecidableRel object.graph.Adj := object.input.decideAdj
  exact (object.graph.neighborFinset vertex ∩ profile.core).card

/-- Positive deficiency `max(0, 3 - d_core(v))`. -/
def positiveDeficiencyAt (vertex : V) : Nat :=
  3 - profile.internalDegree vertex

def positiveDeficiency : Nat :=
  ∑ vertex ∈ profile.core, profile.positiveDeficiencyAt vertex

/-- Ambient degree surplus assigned at one center. -/
def surplusAt (object : FiniteObject V) (center : V) : Nat :=
  object.degree center - 3

def assignedSurplus : Nat :=
  ∑ center ∈ profile.assignedCenters, surplusAt object center

/-- Ordinary core-vertex charge `delta^+ - 1/4`, in quarter units. -/
def coreQuarterChargeAt (vertex : V) : Int :=
  4 * (profile.positiveDeficiencyAt vertex : Int) - 1

def coreQuarterCharge : Int :=
  ∑ vertex ∈ profile.core, profile.coreQuarterChargeAt vertex

/-- Extra assigned-center entry `-(d_G(h)-3)-1/4`, in quarter units. -/
def centerQuarterChargeAt (object : FiniteObject V) (center : V) : Int :=
  -4 * (surplusAt object center : Int) - 1

def centerQuarterCharge : Int :=
  ∑ center ∈ profile.assignedCenters, centerQuarterChargeAt object center

/-- The manuscript's augmented Type B ledger, in quarter units. -/
def augmentedQuarterCharge : Int :=
  profile.coreQuarterCharge + profile.centerQuarterCharge

/-- Four times `def^+(X) - sigma(X) - |X|/4`. -/
def netQuarterCharge : Int :=
  4 * (profile.positiveDeficiency : Int) -
    4 * (profile.assignedSurplus : Int) -
      (profile.core.card : Int)

theorem coreQuarterCharge_eq :
    profile.coreQuarterCharge =
      4 * (profile.positiveDeficiency : Int) -
        (profile.core.card : Int) := by
  classical
  unfold coreQuarterCharge positiveDeficiency coreQuarterChargeAt
  rw [Finset.sum_sub_distrib]
  rw [← Finset.mul_sum]
  norm_cast
  simp

theorem centerQuarterCharge_eq :
    profile.centerQuarterCharge =
      -4 * (profile.assignedSurplus : Int) -
        (profile.assignedCenters.card : Int) := by
  classical
  unfold centerQuarterCharge assignedSurplus centerQuarterChargeAt
  rw [Finset.sum_sub_distrib]
  rw [← Finset.mul_sum]
  norm_cast
  simp

/-- Exact B-ledger accounting identity. -/
theorem netQuarterCharge_eq_augmented_add_centers :
    profile.netQuarterCharge =
      profile.augmentedQuarterCharge +
        (profile.assignedCenters.card : Int) := by
  unfold augmentedQuarterCharge
  rw [profile.coreQuarterCharge_eq, profile.centerQuarterCharge_eq]
  unfold netQuarterCharge
  omega

/-- A nonnegative augmented ledger implies nonnegative net charge. -/
theorem netQuarterCharge_nonnegative_of_augmented
    (nonnegative : 0 ≤ profile.augmentedQuarterCharge) :
    0 ≤ profile.netQuarterCharge := by
  rw [profile.netQuarterCharge_eq_augmented_add_centers]
  exact Int.add_nonneg nonnegative (by positivity)

/-- The quantity actually targeted after omitting the counted core charge of
each assigned high center is definitionally the net charge itself. -/
def reducedQuarterLedger : Int :=
  profile.augmentedQuarterCharge + (profile.assignedCenters.card : Int)

theorem reducedQuarterLedger_eq_netQuarterCharge :
    profile.reducedQuarterLedger = profile.netQuarterCharge := by
  unfold reducedQuarterLedger
  rw [← netQuarterCharge_eq_augmented_add_centers]

/-! ## Exact post-selection decomposition -/

/-- Core vertices consumed by a selected local ledger together with the
assigned high centers whose ordinary core charges must be retained. -/
noncomputable def processedCore (used : Finset V) : Finset V := by
  letI : DecidableEq V := object.input.vertices.decEq
  exact used ∪ profile.assignedCenters

/-- Literal unprocessed induced core after removing selected vertices and
assigned centers. -/
noncomputable def remainingCore (used : Finset V) : Finset V := by
  letI : DecidableEq V := object.input.vertices.decEq
  exact profile.core \ profile.processedCore used

noncomputable def reconstructedCore (used : Finset V) : Finset V := by
  letI : DecidableEq V := object.input.vertices.decEq
  exact profile.processedCore used ∪ profile.remainingCore used

theorem processedCore_subset_core (used : Finset V)
    (used_subset : used ⊆ profile.core)
    (centers_subset : profile.assignedCenters ⊆ profile.core) :
    profile.processedCore used ⊆ profile.core := by
  letI : DecidableEq V := object.input.vertices.decEq
  intro vertex member
  unfold processedCore at member
  rcases Finset.mem_union.mp member with usedMember | centerMember
  · exact used_subset usedMember
  · exact centers_subset centerMember

theorem core_eq_reconstructedCore (used : Finset V)
    (used_subset : used ⊆ profile.core)
    (centers_subset : profile.assignedCenters ⊆ profile.core) :
    profile.core = profile.reconstructedCore used := by
  letI : DecidableEq V := object.input.vertices.decEq
  unfold reconstructedCore
  symm
  exact Finset.union_sdiff_of_subset
    (profile.processedCore_subset_core used used_subset centers_subset)

/-- Exact core-charge partition for any selected used set disjoint from the
assigned centers. -/
theorem coreQuarterCharge_eq_used_add_centers_add_remaining
    (used : Finset V)
    (used_subset : used ⊆ profile.core)
    (centers_subset : profile.assignedCenters ⊆ profile.core)
    (used_disjoint : Disjoint used profile.assignedCenters) :
    profile.coreQuarterCharge =
      (∑ vertex ∈ used, profile.coreQuarterChargeAt vertex) +
      (∑ center ∈ profile.assignedCenters,
        profile.coreQuarterChargeAt center) +
      ∑ vertex ∈ profile.remainingCore used,
        profile.coreQuarterChargeAt vertex := by
  letI : DecidableEq V := object.input.vertices.decEq
  change (∑ vertex ∈ profile.core,
    profile.coreQuarterChargeAt vertex) = _
  rw [profile.core_eq_reconstructedCore used used_subset centers_subset]
  unfold reconstructedCore remainingCore
  rw [Finset.sum_union Finset.disjoint_sdiff]
  unfold processedCore
  rw [Finset.sum_union used_disjoint]

/-- Every retained assigned-center core charge becomes nonnegative after its
one-unit reduced-ledger correction. -/
theorem centerCoreCharge_add_card_nonnegative :
    0 ≤
      (∑ center ∈ profile.assignedCenters,
        profile.coreQuarterChargeAt center) +
      (profile.assignedCenters.card : Int) := by
  have pointwise : ∀ center ∈ profile.assignedCenters,
      0 ≤ profile.coreQuarterChargeAt center + 1 := by
    intro center _member
    unfold coreQuarterChargeAt
    omega
  have total : 0 ≤ ∑ center ∈ profile.assignedCenters,
      (profile.coreQuarterChargeAt center + 1) :=
    Finset.sum_nonneg pointwise
  rw [Finset.sum_add_distrib] at total
  simpa using total

/-- Exact reduced-ledger identity after selecting a disjoint used core. -/
theorem netQuarterCharge_eq_processed_add_centerCorrection_add_remaining
    (used : Finset V)
    (used_subset : used ⊆ profile.core)
    (centers_subset : profile.assignedCenters ⊆ profile.core)
    (used_disjoint : Disjoint used profile.assignedCenters) :
    profile.netQuarterCharge =
      (profile.centerQuarterCharge +
        ∑ vertex ∈ used, profile.coreQuarterChargeAt vertex) +
      ((∑ center ∈ profile.assignedCenters,
          profile.coreQuarterChargeAt center) +
        (profile.assignedCenters.card : Int)) +
      ∑ vertex ∈ profile.remainingCore used,
        profile.coreQuarterChargeAt vertex := by
  rw [profile.netQuarterCharge_eq_augmented_add_centers]
  unfold augmentedQuarterCharge
  rw [profile.coreQuarterCharge_eq_used_add_centers_add_remaining used
    used_subset centers_subset used_disjoint]
  omega

/-- Exact state-space split: once the selected center-plus-used-core term is
nonnegative, either the net charge is nonnegative or the literal remaining
core has negative charge. -/
theorem netQuarterCharge_nonnegative_or_remaining_negative
    (used : Finset V)
    (used_subset : used ⊆ profile.core)
    (centers_subset : profile.assignedCenters ⊆ profile.core)
    (used_disjoint : Disjoint used profile.assignedCenters)
    (processed_nonnegative :
      0 ≤ profile.centerQuarterCharge +
        ∑ vertex ∈ used, profile.coreQuarterChargeAt vertex) :
    0 ≤ profile.netQuarterCharge ∨
      (∑ vertex ∈ profile.remainingCore used,
        profile.coreQuarterChargeAt vertex) < 0 := by
  by_cases remaining : 0 ≤ ∑ vertex ∈ profile.remainingCore used,
      profile.coreQuarterChargeAt vertex
  · left
    rw [profile.netQuarterCharge_eq_processed_add_centerCorrection_add_remaining
      used used_subset centers_subset used_disjoint]
    exact Int.add_nonneg
      (Int.add_nonneg processed_nonnegative
        profile.centerCoreCharge_add_card_nonnegative)
      remaining
  · right
    omega

end Profile

end StructuralExhaustion.Graph.AssignedSupportCharge
