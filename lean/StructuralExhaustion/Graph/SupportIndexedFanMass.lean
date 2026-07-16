import StructuralExhaustion.CT14.Automation
import StructuralExhaustion.Core.EnumerationCombinators
import Mathlib.Tactic

namespace StructuralExhaustion.Graph.SupportIndexedFanMass

open StructuralExhaustion
open scoped BigOperators

universe uSupport uCenter uOccurrence uAmbient uBranch

/-!
# Support-indexed two-role fan-mass aggregation

Unlike a role--center surrogate, the CT14 members here are the actual residual
supports.  A separate finite incidence type records every center token carried
by a support.  Injectivity of the tagged incidence `(role, center)` is the
precise input expressing disjoint center sets within each of the two roles.
-/

inductive Role
  | ordinary
  | grouped
  deriving DecidableEq

@[implicit_reducible] def roles : FinEnum Role :=
  @FinEnum.ofNodupList Role inferInstance [.ordinary, .grouped]
    (by intro role; cases role <;> simp)
    (by simp)

structure Profile (Support : Type uSupport) (Center : Type uCenter)
    (Occurrence : Type uOccurrence) where
  supports : FinEnum Support
  centers : FinEnum Center
  occurrences : FinEnum Occurrence
  role : Support → Role
  occurrenceSupport : Occurrence → Support
  occurrenceCenter : Occurrence → Center
  supportDecidableEq : DecidableEq Support
  centerSurplus : Center → Nat
  deficit : Support → Nat
  extracted : Support → Prop
  extractedDecidable : ∀ support, Decidable (extracted support)
  coefficient : Nat
  /-- The local per-support estimate proved by the semantic producer. -/
  localBound : ∀ support, ¬ extracted support →
    deficit support ≤ coefficient *
      (∑ occurrence : Occurrence,
        @ite Nat (occurrenceSupport occurrence = support)
          (supportDecidableEq (occurrenceSupport occurrence) support)
          (centerSurplus (occurrenceCenter occurrence)) 0)
  /-- Within either role, distinct supports have disjoint center-token sets;
  repeated copies of a token inside one support are excluded as well. -/
  withinRoleDisjoint : Function.Injective (fun occurrence ↦
    (role (occurrenceSupport occurrence), occurrenceCenter occurrence))

namespace Profile

variable {Support : Type uSupport} {Center : Type uCenter}
  {Occurrence : Type uOccurrence}
  (profile : Profile Support Center Occurrence)

def supportTokenMass (profile : Profile Support Center Occurrence)
    (support : Support) : Nat := by
  letI : FinEnum Occurrence := profile.occurrences
  letI : DecidableEq Support := profile.supportDecidableEq
  exact ∑ occurrence : Occurrence,
    if profile.occurrenceSupport occurrence = support then
      profile.centerSurplus (profile.occurrenceCenter occurrence) else 0

def retainedDeficit (profile : Profile Support Center Occurrence)
    (support : Support) : Nat :=
  @ite Nat (profile.extracted support) (profile.extractedDecidable support)
    0 (profile.deficit support)

def retainedCapacity (profile : Profile Support Center Occurrence)
    (support : Support) : Nat :=
  @ite Nat (profile.extracted support) (profile.extractedDecidable support)
    0 (profile.coefficient * profile.supportTokenMass support)

def capability (profile : Profile Support Center Occurrence)
    (problem : Core.Problem.{uAmbient, uBranch}) :
    CT14.Capability problem where
  Member := Support
  members := profile.supports
  Label := Role
  labelDecidableEq := inferInstance
  memberLowerMass := fun _ support ↦ profile.retainedDeficit support
  memberCapacity := fun _ support ↦ some (profile.retainedCapacity support)
  memberLabel := fun _ support ↦ some (profile.role support)

def input (profile : Profile Support Center Occurrence)
    {problem : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext problem) :
    CT14.Input (profile.capability problem) context := ⟨⟩

def run (profile : Profile Support Center Occurrence)
    {problem : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext problem) :
    CT14.ExecutionResult (profile.capability problem) context :=
  CT14.run (profile.capability problem) context (profile.input context)

def residualMass (profile : Profile Support Center Occurrence) : Nat := by
  letI : FinEnum Support := profile.supports
  exact ∑ support : Support, profile.retainedDeficit support

def carriedTokenMass (profile : Profile Support Center Occurrence) : Nat := by
  letI : FinEnum Support := profile.supports
  exact ∑ support : Support, profile.supportTokenMass support

def globalSurplus (profile : Profile Support Center Occurrence) : Nat := by
  letI : FinEnum Center := profile.centers
  exact ∑ center : Center, profile.centerSurplus center

/-- Exact primitive-check ledger for the uncached representation.  The
capacity-presence scan and upper-capacity fold each recompute a support token
mass by scanning all incidences.  The remaining lower-mass and label scans are
linear in supports, followed by one comparison.  This is local quadratic work;
it does not enumerate ambient graphs or subsets of an ambient vertex universe. -/
def checks (profile : Profile Support Center Occurrence) : Nat :=
  2 * profile.supports.card * profile.occurrences.card +
    2 * profile.supports.card + 1

theorem retainedDeficit_le_capacity (support : Support) :
    profile.retainedDeficit support ≤ profile.retainedCapacity support := by
  by_cases extracted : profile.extracted support
  · simp [retainedDeficit, retainedCapacity, extracted]
  · simpa [retainedDeficit, retainedCapacity, supportTokenMass, extracted]
      using profile.localBound support extracted

theorem lowerMass_le_upperCapacity
    {problem : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext problem) :
    CT14.lowerMass (profile.capability problem) context ≤
      CT14.upperCapacity (profile.capability problem) context := by
  have auxiliary : ∀ values : List Support,
      (values.map profile.retainedDeficit).sum ≤
        (values.map profile.retainedCapacity).sum := by
    intro values
    induction values with
    | nil => simp
    | cons support tail ih =>
        simp only [List.map_cons, List.sum_cons]
        exact Nat.add_le_add (profile.retainedDeficit_le_capacity support) ih
  exact auxiliary profile.supports.orderedValues

theorem carriedTokenMass_eq_occurrenceMass :
    profile.carriedTokenMass =
      letI : FinEnum Occurrence := profile.occurrences
      ∑ occurrence : Occurrence,
        profile.centerSurplus (profile.occurrenceCenter occurrence) := by
  letI : FinEnum Support := profile.supports
  letI : FinEnum Occurrence := profile.occurrences
  unfold carriedTokenMass supportTokenMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro occurrence _
  simp_rw [eq_comm]
  rw [Finset.sum_ite_eq' Finset.univ
    (profile.occurrenceSupport occurrence)]
  simp

/-- The within-role disjointness input yields at most one occurrence for each
role--center token.  Since there are exactly two roles, all support incidences
carry at most twice the global center surplus. -/
theorem occurrenceMass_le_two_mul_globalSurplus :
    (letI : FinEnum Occurrence := profile.occurrences
      ∑ occurrence : Occurrence,
        profile.centerSurplus (profile.occurrenceCenter occurrence)) ≤
      2 * profile.globalSurplus := by
  letI : FinEnum Occurrence := profile.occurrences
  letI : FinEnum Center := profile.centers
  letI : FinEnum Role := roles
  let tagged : Occurrence → Role × Center := fun occurrence ↦
    (profile.role (profile.occurrenceSupport occurrence),
      profile.occurrenceCenter occurrence)
  calc
    (∑ occurrence : Occurrence,
        profile.centerSurplus (profile.occurrenceCenter occurrence)) =
        ∑ taggedValue ∈ Finset.univ.image tagged,
          profile.centerSurplus taggedValue.2 := by
      rw [Finset.sum_image profile.withinRoleDisjoint.injOn]
    _ ≤ ∑ taggedValue : Role × Center,
          profile.centerSurplus taggedValue.2 := by
      apply Finset.sum_le_sum_of_subset
      exact Finset.image_subset_iff.mpr (by simp)
    _ = 2 * profile.globalSurplus := by
      rw [Fintype.sum_prod_type]
      change (∑ center : Center, profile.centerSurplus center) +
          (∑ center : Center, profile.centerSurplus center) = _
      simp [globalSurplus, two_mul]

theorem carriedTokenMass_le_two_mul_globalSurplus :
    profile.carriedTokenMass ≤ 2 * profile.globalSurplus := by
  rw [profile.carriedTokenMass_eq_occurrenceMass]
  exact profile.occurrenceMass_le_two_mul_globalSurplus

theorem residualMass_le_coefficient_mul_carriedTokenMass :
    profile.residualMass ≤
      profile.coefficient * profile.carriedTokenMass := by
  letI : FinEnum Support := profile.supports
  unfold residualMass carriedTokenMass
  calc
    (∑ support : Support, profile.retainedDeficit support) ≤
        ∑ support : Support, profile.retainedCapacity support :=
      Finset.sum_le_sum fun support _ ↦
        profile.retainedDeficit_le_capacity support
    _ ≤ ∑ support : Support,
        profile.coefficient * profile.supportTokenMass support := by
      apply Finset.sum_le_sum
      intro support _
      by_cases extracted : profile.extracted support <;>
        simp [retainedCapacity, extracted]
    _ = profile.coefficient *
        ∑ support : Support, profile.supportTokenMass support := by
      simp [Finset.mul_sum]

theorem residualMass_le_two_mul_coefficient_mul_globalSurplus :
    profile.residualMass ≤
      (2 * profile.coefficient) * profile.globalSurplus := by
  calc
    profile.residualMass ≤
        profile.coefficient * profile.carriedTokenMass :=
      profile.residualMass_le_coefficient_mul_carriedTokenMass
    _ ≤ profile.coefficient * (2 * profile.globalSurplus) :=
      Nat.mul_le_mul_left _ profile.carriedTokenMass_le_two_mul_globalSurplus
    _ = (2 * profile.coefficient) * profile.globalSurplus := by
      ac_rfl

theorem run_terminal
    {problem : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext problem) :
    (profile.run context).terminal = .capacity :=
  CT14.run_terminal_capacity_of_complete
    (profile.capability problem) context (profile.input context)
    (fun support ↦ ⟨profile.retainedCapacity support, rfl⟩)
    (fun support ↦ ⟨profile.role support, rfl⟩)
    (profile.lowerMass_le_upperCapacity context)

theorem run_trace
    {problem : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext problem) :
    (profile.run context).trace =
      [.entry, .lowerMass, .memberScan, .upperCapacity, .comparison,
        .capacityTerminal] :=
  CT14.run_trace_capacity_of_complete
    (profile.capability problem) context (profile.input context)
    (fun support ↦ ⟨profile.retainedCapacity support, rfl⟩)
    (fun support ↦ ⟨profile.role support, rfl⟩)
    (profile.lowerMass_le_upperCapacity context)

structure VerifiedStage {problem : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext problem) : Prop where
  terminal : (profile.run context).terminal = .capacity
  trace : (profile.run context).trace =
    [.entry, .lowerMass, .memberScan, .upperCapacity, .comparison,
      .capacityTerminal]
  verified : (profile.run context).outcome.Valid
  traceValid : @CT14.Graph.ValidTrace problem (profile.capability problem)
    context (profile.run context).trace
  total : ∃ result : CT14.ExecutionResult (profile.capability problem) context,
    result.outcome.Valid ∧ @CT14.Graph.ValidTrace problem
      (profile.capability problem) context result.trace
  massBound : profile.residualMass ≤
    (2 * profile.coefficient) * profile.globalSurplus
  workExact : profile.checks =
    2 * profile.supports.card * profile.occurrences.card +
      2 * profile.supports.card + 1
  quadraticWorkBound : profile.checks ≤
    3 * (profile.supports.card + 1) * (profile.occurrences.card + 1)

def verifiedStage {problem : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext problem) : profile.VerifiedStage context where
  terminal := profile.run_terminal context
  trace := profile.run_trace context
  verified := CT14.run_verified (profile.capability problem) context
    (profile.input context)
  traceValid := CT14.run_trace_valid (profile.capability problem) context
    (profile.input context)
  total := CT14.run_total (profile.capability problem) context
    (profile.input context)
  massBound := profile.residualMass_le_two_mul_coefficient_mul_globalSurplus
  workExact := rfl
  quadraticWorkBound := by
    unfold checks
    nlinarith [Nat.zero_le profile.supports.card,
      Nat.zero_le profile.occurrences.card]

end Profile

end StructuralExhaustion.Graph.SupportIndexedFanMass
