import StructuralExhaustion.CT14.Automation
import StructuralExhaustion.Core.EnumerationCombinators
import Mathlib.Tactic

namespace StructuralExhaustion.Graph.TwoRoleFanMass

open StructuralExhaustion

universe uCenter uAmbient uBranch

/-!
# Two-role fan-mass aggregation

The member universe is definitionally `Role × Center`.  Hence one center can
occur at most once in the ordinary role and once in the grouped-envelope role;
the factor two is proved by the framework rather than supplied as an aggregate
hypothesis.  Inactive pairs contribute zero.  Active entries are either
extracted to a distinguished downstream route or charged by predecessor
semantic evidence to their actual center surplus.
-/

inductive Role
  | ordinary
  | grouped
  deriving DecidableEq

@[implicit_reducible] def roles : FinEnum Role :=
  @FinEnum.ofNodupList Role inferInstance [.ordinary, .grouped]
    (by intro role; cases role <;> simp)
    (by simp)

structure Profile (Center : Type uCenter) where
  centers : FinEnum Center
  centerSurplus : Center → Nat
  active : Role → Center → Prop
  activeDecidable : ∀ role center, Decidable (active role center)
  deficit : Role → Center → Nat
  extracted : Role → Center → Prop
  extractedDecidable : ∀ role center, Decidable (extracted role center)
  coefficient : Nat
  localBound : ∀ role center, active role center → ¬ extracted role center →
    deficit role center ≤ coefficient * centerSurplus center

namespace Profile

variable {Center : Type uCenter} (profile : Profile Center)

abbrev Entry (Center : Type uCenter) := Role × Center

@[implicit_reducible]
def entries (profile : Profile Center) : FinEnum (Entry Center) :=
  @FinEnum.ofNodupList (Entry Center)
    (by
      letI : DecidableEq Center := profile.centers.decEq
      exact inferInstance)
    (profile.centers.orderedValues.map (Role.ordinary, ·) ++
      profile.centers.orderedValues.map (Role.grouped, ·))
    (by
      intro entry
      cases entry with
      | mk role center =>
          cases role <;> simp)
    (by
      apply List.Nodup.append
      · exact profile.centers.nodup_orderedValues.map
          (fun _ _ equal => Prod.mk.inj equal |>.2)
      · exact profile.centers.nodup_orderedValues.map
          (fun _ _ equal => Prod.mk.inj equal |>.2)
      · intro pair ordinaryMem groupedMem
        rcases List.mem_map.mp ordinaryMem with ⟨center, _centerMem, rfl⟩
        simp at groupedMem)

def retainedDeficit (profile : Profile Center) (entry : Entry Center) : Nat :=
  @ite Nat (profile.active entry.1 entry.2)
    (profile.activeDecidable entry.1 entry.2)
    (@ite Nat (profile.extracted entry.1 entry.2)
      (profile.extractedDecidable entry.1 entry.2)
      0 (profile.deficit entry.1 entry.2)) 0

def retainedCapacity (profile : Profile Center) (entry : Entry Center) : Nat :=
  @ite Nat (profile.active entry.1 entry.2)
    (profile.activeDecidable entry.1 entry.2)
    (@ite Nat (profile.extracted entry.1 entry.2)
      (profile.extractedDecidable entry.1 entry.2)
      0 (profile.coefficient * profile.centerSurplus entry.2)) 0

def capability (profile : Profile Center)
    (problem : Core.Problem.{uAmbient, uBranch}) :
    CT14.Capability problem where
  Member := Entry Center
  members := profile.entries
  Label := Role
  labelDecidableEq := inferInstance
  memberLowerMass := fun _ entry => profile.retainedDeficit entry
  memberCapacity := fun _ entry => some (profile.retainedCapacity entry)
  memberLabel := fun _ entry => some entry.1

def input (profile : Profile Center)
    {problem : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext problem) :
    CT14.Input (profile.capability problem) context := ⟨⟩

def run (profile : Profile Center)
    {problem : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext problem) :
    CT14.ExecutionResult (profile.capability problem) context :=
  CT14.run (profile.capability problem) context (profile.input context)

def residualMass (profile : Profile Center) : Nat :=
  (profile.entries.orderedValues.map profile.retainedDeficit).sum

def globalSurplus (profile : Profile Center) : Nat :=
  (profile.centers.orderedValues.map profile.centerSurplus).sum

/-- Exact primitive-check ledger: lower-mass evaluation, capacity-presence
scan, label-presence scan, and upper-capacity evaluation each inspect every
role--center entry once; the final comparison costs one check.  The structural
two-role multiplicity theorem is proof-only and performs no additional fold. -/
def checks (profile : Profile Center) : Nat := 4 * profile.entries.card + 1

theorem retainedDeficit_le_capacity (entry : Entry Center) :
    profile.retainedDeficit entry ≤ profile.retainedCapacity entry := by
  by_cases active : profile.active entry.1 entry.2
  · by_cases extracted : profile.extracted entry.1 entry.2
    · simp [retainedDeficit, retainedCapacity, active, extracted]
    · simpa [retainedDeficit, retainedCapacity, active, extracted] using
        profile.localBound entry.1 entry.2 active extracted
  · simp [retainedDeficit, retainedCapacity, active]

theorem lowerMass_le_upperCapacity
    {problem : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext problem) :
    CT14.lowerMass (profile.capability problem) context ≤
      CT14.upperCapacity (profile.capability problem) context := by
  have auxiliary : ∀ values : List (Entry Center),
      (values.map profile.retainedDeficit).sum ≤
        (values.map profile.retainedCapacity).sum := by
      intro values
      induction values with
      | nil => simp
      | cons entry tail ih =>
          simp only [List.map_cons, List.sum_cons]
          exact Nat.add_le_add (profile.retainedDeficit_le_capacity entry) ih
  exact auxiliary profile.entries.orderedValues

theorem retainedCapacity_le_full (entry : Entry Center) :
    profile.retainedCapacity entry ≤
      profile.coefficient * profile.centerSurplus entry.2 := by
  by_cases active : profile.active entry.1 entry.2
  · by_cases extracted : profile.extracted entry.1 entry.2 <;>
      simp [retainedCapacity, active, extracted]
  · simp [retainedCapacity, active]

theorem capacitySum_le_full :
    (profile.entries.orderedValues.map profile.retainedCapacity).sum ≤
      (profile.entries.orderedValues.map
        (fun entry => profile.coefficient * profile.centerSurplus entry.2)).sum := by
  have auxiliary : ∀ values : List (Entry Center),
      (values.map profile.retainedCapacity).sum ≤
        (values.map
          (fun entry => profile.coefficient * profile.centerSurplus entry.2)).sum := by
      intro values
      induction values with
      | nil => simp
      | cons entry tail ih =>
          simp only [List.map_cons, List.sum_cons]
          exact Nat.add_le_add (profile.retainedCapacity_le_full entry) ih
  exact auxiliary profile.entries.orderedValues

theorem fullCapacity_eq_twoRole :
    (profile.entries.orderedValues.map
      (fun entry => profile.coefficient * profile.centerSurplus entry.2)).sum =
      (2 * profile.coefficient) * profile.globalSurplus := by
  rw [profile.entries.sum_orderedValues]
  unfold globalSurplus
  rw [profile.centers.sum_orderedValues]
  let centerFintype : Fintype Center :=
    @FinEnum.instFintype Center profile.centers
  let roleFintype : Fintype Role :=
    @FinEnum.instFintype Role roles
  let productFintype : Fintype (Role × Center) :=
    @instFintypeProd Role Center roleFintype centerFintype
  let entryFintype : Fintype (Entry Center) :=
    @FinEnum.instFintype (Entry Center) profile.entries
  have entryUnivEq :
      @Finset.univ (Entry Center) entryFintype =
        @Finset.univ (Role × Center) productFintype := by
    ext entry
    simp
  have centerUnivEq :
      @Finset.univ Center (@FinEnum.instFintype Center profile.centers) =
        @Finset.univ Center centerFintype := by
    ext center
    simp
  rw [entryUnivEq, centerUnivEq]
  letI : Fintype Center := centerFintype
  letI : Fintype Role := roleFintype
  rw [Fintype.sum_prod_type]
  change (∑ center : Center,
      profile.coefficient * profile.centerSurplus center) +
      (∑ center : Center,
        profile.coefficient * profile.centerSurplus center) = _
  rw [← two_mul]
  simp_rw [← Finset.mul_sum]
  ring

theorem residualMass_le_two_mul_coefficient_mul_globalSurplus :
    profile.residualMass ≤
      (2 * profile.coefficient) * profile.globalSurplus := by
  calc
    profile.residualMass ≤
        (profile.entries.orderedValues.map profile.retainedCapacity).sum := by
      unfold residualMass
      have auxiliary : ∀ values : List (Entry Center),
          (values.map profile.retainedDeficit).sum ≤
            (values.map profile.retainedCapacity).sum := by
        intro values
        induction values with
        | nil => simp
        | cons entry tail ih =>
            simp only [List.map_cons, List.sum_cons]
            exact Nat.add_le_add
              (profile.retainedDeficit_le_capacity entry) ih
      exact auxiliary profile.entries.orderedValues
    _ ≤ (profile.entries.orderedValues.map
        (fun entry => profile.coefficient * profile.centerSurplus entry.2)).sum :=
      profile.capacitySum_le_full
    _ = (2 * profile.coefficient) * profile.globalSurplus :=
      profile.fullCapacity_eq_twoRole

theorem run_terminal
    {problem : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext problem) :
    (profile.run context).terminal = .capacity :=
  CT14.run_terminal_capacity_of_complete
    (profile.capability problem) context (profile.input context)
    (fun entry => ⟨profile.retainedCapacity entry, rfl⟩)
    (fun entry => ⟨entry.1, rfl⟩)
    (profile.lowerMass_le_upperCapacity context)

theorem run_trace
    {problem : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext problem) :
    (profile.run context).trace =
      [.entry, .lowerMass, .memberScan, .upperCapacity, .comparison,
        .capacityTerminal] :=
  CT14.run_trace_capacity_of_complete
    (profile.capability problem) context (profile.input context)
    (fun entry => ⟨profile.retainedCapacity entry, rfl⟩)
    (fun entry => ⟨entry.1, rfl⟩)
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
  polynomial : profile.checks ≤ 9 * (profile.centers.card + 1)

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
  polynomial := by
    letI : FinEnum Center := profile.centers
    letI : FinEnum Role := roles
    letI : FinEnum (Entry Center) := profile.entries
    have cardEq : profile.entries.card = 2 * profile.centers.card := by
      rw [FinEnum.card_eq_fintypeCard, FinEnum.card_eq_fintypeCard]
      rw [Fintype.card_prod]
      have roleCard : Fintype.card Role = 2 := by native_decide
      rw [roleCard]
    unfold checks
    rw [cardEq]
    omega

end Profile

end StructuralExhaustion.Graph.TwoRoleFanMass
