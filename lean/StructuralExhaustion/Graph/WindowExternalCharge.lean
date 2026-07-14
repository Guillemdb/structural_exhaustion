import Mathlib.Data.Fintype.BigOperators
import StructuralExhaustion.Graph.HybridFanIncidence

namespace StructuralExhaustion.Graph.WindowExternalCharge

open StructuralExhaustion
open scoped BigOperators

universe u

/-!
# Window incidences are literal external shoulder corrections

For a fan whose counted core lies on the remainder side, every assigned
incidence ending on the disjoint window side leaves that core.  This file
turns that pointwise fact into the exact finite cardinal inequality used by
the Type B charge ledger.  The proof is by an injection between explicit
finite subtypes; it performs no subset search.
-/

variable {V : Type u}
variable {base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
variable {object : FiniteObject V} {baseline : base.problem.Baseline object}
variable {center : V} (centerHigh : 4 ≤ object.degree center)
variable (deletionCritical : ∀ dart : object.graph.Dart,
  object.degree dart.fst = 3 ∨ object.degree dart.snd = 3)

def portShoulder (port : HighCenterPort.Port object center) (side : Bool) : V :=
  if side then
    HighCenterPort.secondShoulder object center centerHigh deletionCritical port
  else
    HighCenterPort.firstShoulder object center centerHigh deletionCritical port

def ExternalAt
    (Assigned : FanClosedPort.LocalCarrier V → Prop)
    (core : Finset V) (port : HighCenterPort.Port object center)
    (side : Bool) : Prop :=
  Assigned (HighCenterPort.endpoint object center port,
      portShoulder (object := object) (center := center) centerHigh
        deletionCritical port side) ∧
    portShoulder (object := object) (center := center) centerHigh
      deletionCritical port side ∉ core

@[implicit_reducible]
def externalShoulders
    (Assigned : FanClosedPort.LocalCarrier V → Prop)
    (assignedDecidable : ∀ carrier, Decidable (Assigned carrier))
    (core : Finset V) :
    FinEnum {pair : HighCenterPort.Port object center × Bool //
      ExternalAt (object := object) (center := center) centerHigh
        deletionCritical Assigned core pair.1 pair.2} :=
  Core.Enumeration.subtype
    (Core.Enumeration.prod (HighCenterPort.ports object center)
      Core.Enumeration.bool)
    (fun pair => ExternalAt (object := object) (center := center) centerHigh
      deletionCritical Assigned core pair.1 pair.2)
    (fun pair => by
      letI : DecidableEq V := object.input.vertices.decEq
      letI : Decidable (Assigned
          (HighCenterPort.endpoint object center pair.1,
            portShoulder (object := object) (center := center) centerHigh
              deletionCritical pair.1 pair.2)) := assignedDecidable _
      unfold ExternalAt
      infer_instance)

@[implicit_reducible]
def windowIncidences (profile : FanClosedPort.FanWindowProfile V) :
    FinEnum {incidence : HybridFanIncidence.Incidence
        (object := object) (center := center) profile //
      HybridFanIncidence.incidenceKind (object := object) (center := center)
        profile incidence = .window} :=
  Core.Enumeration.subtype
    (HybridFanIncidence.incidences (object := object) (center := center) profile)
    (fun incidence => HybridFanIncidence.incidenceKind
      (object := object) (center := center) profile incidence = .window)
    (fun _incidence => inferInstance)

theorem incidenceKind_eq_window_iff
    (profile : FanClosedPort.FanWindowProfile V)
    (incidence : HybridFanIncidence.Incidence
      (object := object) (center := center) profile) :
    HybridFanIncidence.incidenceKind (object := object) (center := center)
        profile incidence = .window ↔
      profile.WindowSide
        (HybridFanIncidence.other (object := object) (center := center)
          profile incidence.1 incidence.2) := by
  unfold HybridFanIncidence.incidenceKind HybridFanIncidence.carrier
  split <;> simp_all

/-- A window incidence has the same literal port and shoulder coordinate and
is therefore an assigned shoulder outside any remainder-side core. -/
noncomputable def windowToExternal
    (profile : FanClosedPort.FanWindowProfile V)
    (core : Finset V)
    (coreRemainder : ∀ vertex, vertex ∈ core → profile.RemainderSide vertex) :
    {incidence : HybridFanIncidence.Incidence
        (object := object) (center := center) profile //
      HybridFanIncidence.incidenceKind (object := object) (center := center)
        profile incidence = .window} →
    {pair : HighCenterPort.Port object center × Bool //
      ExternalAt (object := object) (center := center) centerHigh
        deletionCritical profile.Assigned core pair.1 pair.2} := fun incidence => by
  let member := incidence.1.1
  let side := incidence.1.2
  let port := HybridFanIncidence.memberPort
    (object := object) (center := center) profile member
  have otherEq :
      HybridFanIncidence.other (object := object) (center := center)
          profile member side =
        portShoulder (object := object) (center := center) centerHigh
          deletionCritical port side := by
    simpa [portShoulder, port] using
      HybridFanIncidence.other_eq_portShoulder
        (object := object) (center := center) centerHigh deletionCritical
        profile member side
  refine ⟨(port, side), ?_⟩
  constructor
  · have assigned : profile.Assigned
        (member.1, HybridFanIncidence.other (object := object)
          (center := center) profile member side) := by
      simpa [member, side, HybridFanIncidence.carrier] using
        (HybridFanIncidence.carrier_assigned
          (object := object) (center := center) profile incidence.1)
    rw [HybridFanIncidence.endpoint_memberPort
      (object := object) (center := center) profile member]
    simpa only [otherEq] using assigned
  · intro shoulderCore
    have window : profile.WindowSide
        (HybridFanIncidence.other (object := object) (center := center)
          profile member side) :=
      (incidenceKind_eq_window_iff
        (object := object) (center := center) profile incidence.1).1 incidence.2
    exact profile.remainder_not_window _
      (coreRemainder _ (by simpa [otherEq] using shoulderCore)) window

theorem windowToExternal_injective
    (profile : FanClosedPort.FanWindowProfile V)
    (core : Finset V)
    (coreRemainder : ∀ vertex, vertex ∈ core → profile.RemainderSide vertex) :
    Function.Injective
      (windowToExternal (object := object) (center := center) centerHigh
        deletionCritical profile core coreRemainder) := by
  intro left right equal
  have pairEqual := congrArg Subtype.val equal
  have portEqual := congrArg Prod.fst pairEqual
  have sideEqual := congrArg Prod.snd pairEqual
  apply Subtype.ext
  apply Prod.ext
  · apply HybridFanIncidence.memberPort_injective
      (object := object) (center := center) profile
    exact portEqual
  · exact sideEqual

theorem windowIncidences_card_le_externalShoulders_card
    (profile : FanClosedPort.FanWindowProfile V)
    (core : Finset V)
    (coreRemainder : ∀ vertex, vertex ∈ core → profile.RemainderSide vertex) :
    (windowIncidences (object := object) (center := center) profile).card ≤
      (externalShoulders (object := object) (center := center) centerHigh
        deletionCritical profile.Assigned profile.assignedDecidable core).card := by
  letI : FinEnum {incidence : HybridFanIncidence.Incidence
      (object := object) (center := center) profile //
    HybridFanIncidence.incidenceKind (object := object) (center := center)
      profile incidence = .window} :=
    windowIncidences (object := object) (center := center) profile
  letI : FinEnum {pair : HighCenterPort.Port object center × Bool //
      ExternalAt (object := object) (center := center) centerHigh
        deletionCritical profile.Assigned core pair.1 pair.2} :=
    externalShoulders (object := object) (center := center) centerHigh
      deletionCritical profile.Assigned profile.assignedDecidable core
  simpa [FinEnum.card_eq_fintypeCard] using
    Fintype.card_le_of_injective
      (windowToExternal (object := object) (center := center) centerHigh
        deletionCritical profile core coreRemainder)
      (windowToExternal_injective (object := object) (center := center)
        centerHigh deletionCritical profile core coreRemainder)

theorem windowIncidences_card_eq_multiplicity
    (profile : FanClosedPort.FanWindowProfile V) :
    (windowIncidences (object := object) (center := center) profile).card =
      CT14.multiplicity
        (HybridFanIncidence.capability (base := base) (object := object)
          (center := center) profile)
        (HybridFanIncidence.context base object baseline) .window := by
  letI : FinEnum (HybridFanIncidence.Incidence
      (object := object) (center := center) profile) :=
    HybridFanIncidence.incidences (object := object) (center := center) profile
  letI : FinEnum {incidence : HybridFanIncidence.Incidence
      (object := object) (center := center) profile //
    HybridFanIncidence.incidenceKind (object := object) (center := center)
      profile incidence = .window} :=
    windowIncidences (object := object) (center := center) profile
  rw [FinEnum.card_eq_fintypeCard, Fintype.card_subtype]
  have counted := CT14.card_membersWithLabel_eq_multiplicity
    (HybridFanIncidence.capability (base := base) (object := object)
      (center := center) profile)
    (HybridFanIncidence.context base object baseline)
    FanClosedPort.IncidenceKind.window
  rw [← counted]
  unfold CT14.membersWithLabel
  dsimp only [HybridFanIncidence.capability]
  apply congrArg Finset.card
  ext incidence
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    CT14.labelMatches_eq_true_iff, Option.some.injEq]
  constructor
  · intro kind
    exact ⟨by
      simpa only [List.mem_toFinset] using
        (HybridFanIncidence.incidences (object := object) (center := center)
          profile).mem_orderedValues incidence, kind⟩
  · rintro ⟨_member, kind⟩
    exact kind

@[implicit_reducible]
def externalSides
    (Assigned : FanClosedPort.LocalCarrier V → Prop)
    (assignedDecidable : ∀ carrier, Decidable (Assigned carrier))
    (core : Finset V) (port : HighCenterPort.Port object center) :
    FinEnum {side : Bool //
      ExternalAt (object := object) (center := center) centerHigh
        deletionCritical Assigned core port side} :=
  Core.Enumeration.subtype Core.Enumeration.bool
    (ExternalAt (object := object) (center := center) centerHigh
      deletionCritical Assigned core port)
    (fun side => by
      letI : DecidableEq V := object.input.vertices.decEq
      letI : Decidable (Assigned
          (HighCenterPort.endpoint object center port,
            portShoulder (object := object) (center := center) centerHigh
              deletionCritical port side)) := assignedDecidable _
      unfold ExternalAt
      infer_instance)

theorem localExternalCard_eq_count
    (Assigned : FanClosedPort.LocalCarrier V → Prop)
    (assignedDecidable : ∀ carrier, Decidable (Assigned carrier))
    (core : Finset V) (port : HighCenterPort.Port object center) :
    (externalSides (object := object) (center := center) centerHigh
      deletionCritical Assigned assignedDecidable core port).card =
      AssignedFanCharge.externalAssignedShoulderCount object center centerHigh
        deletionCritical Assigned assignedDecidable core port := by
  letI : FinEnum {side : Bool //
      ExternalAt (object := object) (center := center) centerHigh
        deletionCritical Assigned core port side} :=
    externalSides (object := object) (center := center) centerHigh
      deletionCritical Assigned assignedDecidable core port
  classical
  rw [FinEnum.card_eq_fintypeCard, Fintype.card_subtype]
  have boolCard (predicate : Bool → Prop) [DecidablePred predicate] :
      (Finset.univ.filter predicate).card =
        (if predicate false then 1 else 0) +
          (if predicate true then 1 else 0) := by
    rw [show (Finset.univ : Finset Bool) = {false, true} by decide]
    by_cases atFalse : predicate false <;>
      by_cases atTrue : predicate true
    all_goals
      rw [Finset.filter_insert, Finset.filter_singleton]
      simp [atFalse, atTrue]
  rw [boolCard]
  by_cases firstAssigned : Assigned
      (HighCenterPort.endpoint object center port,
        HighCenterPort.firstShoulder object center centerHigh
          deletionCritical port) <;>
    by_cases secondAssigned : Assigned
      (HighCenterPort.endpoint object center port,
        HighCenterPort.secondShoulder object center centerHigh
          deletionCritical port) <;>
      by_cases firstCore : HighCenterPort.firstShoulder object center
        centerHigh deletionCritical port ∈ core <;>
        by_cases secondCore : HighCenterPort.secondShoulder object center
          centerHigh deletionCritical port ∈ core
  all_goals
    simp_all [ExternalAt, portShoulder,
      AssignedFanCharge.externalAssignedShoulderCount,
      AssignedFanCharge.firstAssigned, AssignedFanCharge.secondAssigned]

def externalSigmaEquiv
    (Assigned : FanClosedPort.LocalCarrier V → Prop) (core : Finset V) :
    {pair : HighCenterPort.Port object center × Bool //
      ExternalAt (object := object) (center := center) centerHigh
        deletionCritical Assigned core pair.1 pair.2} ≃
    (Σ port : HighCenterPort.Port object center,
      {side : Bool // ExternalAt (object := object) (center := center)
        centerHigh deletionCritical Assigned core port side}) where
  toFun := fun pair => ⟨pair.1.1, ⟨pair.1.2, pair.2⟩⟩
  invFun := fun pair => ⟨(pair.1, pair.2.1), pair.2.2⟩
  left_inv := by intro pair; rfl
  right_inv := by intro pair; rfl

theorem externalShoulders_card_eq_sum
    (Assigned : FanClosedPort.LocalCarrier V → Prop)
    (assignedDecidable : ∀ carrier, Decidable (Assigned carrier))
    (core : Finset V) :
    (externalShoulders (object := object) (center := center) centerHigh
        deletionCritical Assigned assignedDecidable core).card =
      ∑ port ∈ (HighCenterPort.ports object center).orderedValues.toFinset,
        AssignedFanCharge.externalAssignedShoulderCount object center centerHigh
          deletionCritical Assigned assignedDecidable core port := by
  letI : FinEnum {pair : HighCenterPort.Port object center × Bool //
      ExternalAt (object := object) (center := center) centerHigh
        deletionCritical Assigned core pair.1 pair.2} :=
    externalShoulders (object := object) (center := center) centerHigh
      deletionCritical Assigned assignedDecidable core
  letI (port : HighCenterPort.Port object center) :
      FinEnum {side : Bool //
        ExternalAt (object := object) (center := center) centerHigh
          deletionCritical Assigned core port side} :=
    externalSides (object := object) (center := center) centerHigh
      deletionCritical Assigned assignedDecidable core port
  rw [FinEnum.card_eq_fintypeCard]
  calc
    Fintype.card {pair : HighCenterPort.Port object center × Bool //
        ExternalAt (object := object) (center := center) centerHigh
          deletionCritical Assigned core pair.1 pair.2} =
        Fintype.card (Σ port : HighCenterPort.Port object center,
          {side : Bool // ExternalAt (object := object) (center := center)
            centerHigh deletionCritical Assigned core port side}) :=
      Fintype.card_congr
        (externalSigmaEquiv (object := object) (center := center) centerHigh
          deletionCritical Assigned core)
    _ = ∑ port : HighCenterPort.Port object center,
          Fintype.card {side : Bool //
            ExternalAt (object := object) (center := center) centerHigh
              deletionCritical Assigned core port side} :=
      Fintype.card_sigma
    _ = ∑ port : HighCenterPort.Port object center,
          AssignedFanCharge.externalAssignedShoulderCount object center
            centerHigh deletionCritical Assigned assignedDecidable core port := by
      apply Finset.sum_congr rfl
      intro port _member
      simpa [FinEnum.card_eq_fintypeCard] using
        (localExternalCard_eq_count (object := object) (center := center)
          centerHigh deletionCritical Assigned assignedDecidable core port)
    _ = ∑ port ∈ (HighCenterPort.ports object center).orderedValues.toFinset,
          AssignedFanCharge.externalAssignedShoulderCount object center
            centerHigh deletionCritical Assigned assignedDecidable core port := by
      have allPorts :
          (HighCenterPort.ports object center).orderedValues.toFinset =
            (Finset.univ : Finset (HighCenterPort.Port object center)) := by
        ext port
        simp only [List.mem_toFinset, Finset.mem_univ, iff_true]
        exact (HighCenterPort.ports object center).mem_orderedValues port
      rw [allPorts]

/-- Generic finite summation rule used after the graph-specific window
injection has produced a correction bound. -/
theorem sum_weight_add_credit_le_actual
    {Index : Type*} [DecidableEq Index]
    (indices : Finset Index) (weight actual : Index → Int)
    (external : Index → Nat) (credit : Int)
    (creditBound : credit ≤
      (4 : Int) * ↑(∑ index ∈ indices, external index))
    (pointwise : ∀ index ∈ indices,
      weight index + 4 * (external index : Int) ≤ actual index) :
    (∑ index ∈ indices, weight index) + credit ≤
      ∑ index ∈ indices, actual index := by
  have summed :
      ∑ index ∈ indices,
          (weight index + 4 * (external index : Int)) ≤
        ∑ index ∈ indices, actual index := by
    exact Finset.sum_le_sum pointwise
  have sumIdentity :
      ∑ index ∈ indices,
          (weight index + 4 * (external index : Int)) =
        (∑ index ∈ indices, weight index) +
          (4 : Int) * ↑(∑ index ∈ indices, external index) := by
    rw [Finset.sum_add_distrib]
    congr 1
    push_cast
    rw [Finset.mul_sum]
  calc
    _ ≤ (∑ index ∈ indices, weight index) +
          (4 : Int) * ↑(∑ index ∈ indices, external index) :=
      by omega
    _ = ∑ index ∈ indices,
          (weight index + 4 * (external index : Int)) := sumIdentity.symm
    _ ≤ _ := summed

/-- Exact framework bridge: two quarter-units per window incidence are paid
by the four-quarter-unit correction of the corresponding external assigned
shoulder. -/
theorem windowQuarterCredit_le_externalCorrection
    (profile : FanClosedPort.FanWindowProfile V)
    (core : Finset V)
    (coreRemainder : ∀ vertex, vertex ∈ core → profile.RemainderSide vertex) :
    (HybridFanIncidence.windowQuarterCredit
        (base := base) (object := object) (baseline := baseline)
        (center := center) profile : Int) ≤
      4 * (∑ port ∈
        (HighCenterPort.ports object center).orderedValues.toFinset,
          AssignedFanCharge.externalAssignedShoulderCount object center
            centerHigh deletionCritical profile.Assigned
              profile.assignedDecidable core port : Nat) := by
  have cardLe := windowIncidences_card_le_externalShoulders_card
    (object := object) (center := center) centerHigh deletionCritical profile
    core coreRemainder
  rw [windowIncidences_card_eq_multiplicity
    (base := base) (object := object) (baseline := baseline)
    (center := center) profile] at cardLe
  rw [externalShoulders_card_eq_sum (object := object) (center := center)
    centerHigh deletionCritical profile.Assigned profile.assignedDecidable core]
    at cardLe
  unfold HybridFanIncidence.windowQuarterCredit
  have doubled := Nat.mul_le_mul_left 2 cardLe
  have quadrupled : 2 *
      (∑ port ∈ (HighCenterPort.ports object center).orderedValues.toFinset,
        AssignedFanCharge.externalAssignedShoulderCount object center centerHigh
          deletionCritical profile.Assigned profile.assignedDecidable core port) ≤
      4 *
      (∑ port ∈ (HighCenterPort.ports object center).orderedValues.toFinset,
        AssignedFanCharge.externalAssignedShoulderCount object center centerHigh
          deletionCritical profile.Assigned profile.assignedDecidable core port) := by
    omega
  exact_mod_cast doubled.trans quadrupled

end StructuralExhaustion.Graph.WindowExternalCharge
