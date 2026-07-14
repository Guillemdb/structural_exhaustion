import StructuralExhaustion.Core.FiniteWeightedSelection
import StructuralExhaustion.Graph.HybridFanIncidence

namespace StructuralExhaustion.Graph.HybridFanCandidate

open StructuralExhaustion
open scoped BigOperators

universe u

/-!
# Concrete refined-ledger candidates for a positive-deficit fan

The selectable items are the literal two incidences of every cubic-closed fan
member.  Every window incidence is mandatory.  A selection is valid only when
its non-window half-credits pay the exact remaining CT14 demand and none of its
incidences has already been consumed by the ordinary reserve.

The candidate fibre is finite at proof level.  No powerset is evaluated by a
runner or by kernel reduction.
-/

/-- The already occupied part of the ordinary incidence reserve. -/
structure IncidenceReserve (V : Type u) where
  Used : FanClosedPort.LocalCarrier V → Prop
  usedDecidable : ∀ carrier, Decidable (Used carrier)

variable {V : Type u}
variable {base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
variable {object : FiniteObject V} {baseline : base.problem.Baseline object}
variable {center : V} (centerHigh : 4 ≤ object.degree center)
variable (deletionCritical : ∀ dart : object.graph.Dart,
  object.degree dart.fst = 3 ∨ object.degree dart.snd = 3)

abbrev Incidence (profile : FanClosedPort.FanWindowProfile V) :=
  HybridFanIncidence.Incidence (object := object) (center := center) profile

/-- Every positive candidate carries the center and every literal fan
neighbour whose charge occurs in the local fan sum.  Recording the complete
fan, rather than only the cubic-closed members, makes global carrier
disjointness sufficient to prevent hidden reuse of an open fan neighbour. -/
def baseSupport (_profile : FanClosedPort.FanWindowProfile V) : Finset V := by
  letI : DecidableEq V := object.input.vertices.decEq
  exact insert center
    ((HighCenterPort.ports object center).orderedValues.map
      (HighCenterPort.endpoint object center)).toFinset

/-- One selected incidence occupies both of its literal endpoints. -/
def incidenceSupport (profile : FanClosedPort.FanWindowProfile V)
    (incidence : Incidence (object := object) (center := center) profile) :
    Finset V := by
  letI : DecidableEq V := object.input.vertices.decEq
  exact {incidence.1.1,
    HybridFanIncidence.other (object := object) (center := center)
      profile incidence.1 incidence.2}

/-- Exact finite candidate fibre from
`def:typeB-candidate-ledger`, positive-deficit branch. -/
def profile (fanProfile : FanClosedPort.FanWindowProfile V)
    (reserve : IncidenceReserve V) :
    Core.FiniteWeightedSelection.Profile
      (Incidence (object := object) (center := center) fanProfile) V where
  items := HybridFanIncidence.incidences
    (object := object) (center := center) fanProfile
  carrierDecidableEq := object.input.vertices.decEq
  mandatory := fun incidence =>
    HybridFanIncidence.incidenceKind (object := object) (center := center)
      fanProfile incidence = .window
  mandatoryDecidable := fun _incidence => inferInstance
  forbidden := fun incidence => reserve.Used
    (HybridFanIncidence.carrier (object := object) (center := center)
      fanProfile incidence)
  forbiddenDecidable := fun _incidence => reserve.usedDecidable _
  weight := fun incidence =>
    if HybridFanIncidence.incidenceKind (object := object) (center := center)
        fanProfile incidence = .nonWindow then 2 else 0
  required := HybridFanIncidence.remainingNonWindowDemand
    (base := base) (object := object) (baseline := baseline)
    (center := center) fanProfile
  baseSupport := baseSupport (object := object) (center := center) fanProfile
  itemSupport := incidenceSupport (object := object) (center := center) fanProfile

abbrev Candidate (fanProfile : FanClosedPort.FanWindowProfile V)
    (reserve : IncidenceReserve V) :=
  (profile (base := base) (object := object) (baseline := baseline)
    (center := center) fanProfile reserve).Candidate

/-- The all-incidence selection carries exactly the CT14 non-window
multiplicity, in quarter units. -/
theorem allItems_weight_eq_nonWindowQuarterCredit
    (fanProfile : FanClosedPort.FanWindowProfile V)
    (reserve : IncidenceReserve V) :
    (∑ incidence ∈ (profile (base := base) (object := object)
        (baseline := baseline) (center := center) fanProfile reserve).allItems,
      if HybridFanIncidence.incidenceKind (object := object)
          (center := center) fanProfile incidence = .nonWindow
        then 2 else 0) =
      (HybridFanIncidence.nonWindowQuarterCredit
        (base := base) (object := object) (baseline := baseline)
        (center := center) fanProfile : Int) := by
  have counted := CT14.card_membersWithLabel_eq_multiplicity
    (HybridFanIncidence.capability
      (base := base) (object := object) (center := center) fanProfile)
    (HybridFanIncidence.context base object baseline)
    FanClosedPort.IncidenceKind.nonWindow
  have filterEq : CT14.membersWithLabel
      (HybridFanIncidence.capability
        (base := base) (object := object) (center := center) fanProfile)
      (HybridFanIncidence.context base object baseline)
      FanClosedPort.IncidenceKind.nonWindow =
      ((profile (base := base) (object := object) (baseline := baseline)
        (center := center) fanProfile reserve).allItems.filter fun incidence =>
          HybridFanIncidence.incidenceKind (object := object)
            (center := center) fanProfile incidence = .nonWindow) := by
    unfold CT14.membersWithLabel
    dsimp only [HybridFanIncidence.capability, profile]
    unfold Core.FiniteWeightedSelection.Profile.allItems
    apply Finset.ext
    intro incidence
    rw [Finset.mem_filter, Finset.mem_filter]
    simp only [CT14.labelMatches_eq_true_iff, Option.some.injEq]
    constructor
    · rintro ⟨member, kind⟩
      exact ⟨by simpa only [List.mem_toFinset] using member, kind⟩
    · rintro ⟨member, kind⟩
      exact ⟨by simpa only [List.mem_toFinset] using member, kind⟩
  rw [filterEq] at counted
  let selected := (profile (base := base) (object := object)
    (baseline := baseline) (center := center) fanProfile reserve).allItems
  have sumEq :
      (∑ incidence ∈ selected,
        if HybridFanIncidence.incidenceKind (object := object)
            (center := center) fanProfile incidence = .nonWindow
          then (2 : Int) else 0) =
        2 * (selected.filter fun incidence =>
          HybridFanIncidence.incidenceKind (object := object)
            (center := center) fanProfile incidence = .nonWindow).card := by
    classical
    induction selected using Finset.induction_on with
    | empty => simp
    | @insert incidence tail absent ih =>
        by_cases nonWindow : HybridFanIncidence.incidenceKind
            (object := object) (center := center) fanProfile incidence =
              .nonWindow
        · rw [Finset.sum_insert absent, Finset.filter_insert]
          simp [absent, nonWindow, ih]
          omega
        · rw [Finset.sum_insert absent, Finset.filter_insert]
          simp [nonWindow, ih]
  rw [sumEq]
  change ((profile (base := base) (object := object) (baseline := baseline)
    (center := center) fanProfile reserve).allItems.filter fun incidence =>
      HybridFanIncidence.incidenceKind (object := object) (center := center)
        fanProfile incidence = .nonWindow).card = _ at counted
  unfold selected
  rw [HybridFanIncidence.nonWindowQuarterCredit]
  exact_mod_cast congrArg (2 * ·) counted

/-- If none of the literal fan incidences has already been consumed by the
ordinary reserve, the verified CT14 B1 inequality constructs a genuine
positive-deficit candidate. -/
noncomputable def allItemsCandidate
    (fanProfile : FanClosedPort.FanWindowProfile V)
    (reserve : IncidenceReserve V)
    (degreeLeEight : object.degree center ≤ 8)
    (reserveFree : ∀ incidence : Incidence (object := object)
      (center := center) fanProfile,
      ¬reserve.Used (HybridFanIncidence.carrier (object := object)
        (center := center) fanProfile incidence)) :
    Candidate (base := base) (object := object) (baseline := baseline)
      (center := center) fanProfile reserve := by
  apply (profile (base := base) (object := object) (baseline := baseline)
    (center := center) fanProfile reserve).allItemsCandidate
  · exact reserveFree
  · change HybridFanIncidence.remainingNonWindowDemand
        (base := base) (object := object) (baseline := baseline)
        (center := center) fanProfile ≤
      ∑ incidence ∈ (profile (base := base) (object := object)
        (baseline := baseline) (center := center) fanProfile reserve).allItems,
        if HybridFanIncidence.incidenceKind (object := object)
            (center := center) fanProfile incidence = .nonWindow
          then 2 else 0
    rw [allItems_weight_eq_nonWindowQuarterCredit
      (base := base) (object := object) (baseline := baseline)
      (center := center) fanProfile reserve]
    exact HybridFanIncidence.nonWindow_credit_pays_remaining
      (base := base) (object := object) (baseline := baseline)
      (center := center) fanProfile degreeLeEight

/-- Every vertex in the complete declared positive-fan carrier universe is
joined to the center by a path of length at most two using the literal fan
edges. -/
theorem declaredCarrierSupport_reachable
    (fanProfile : FanClosedPort.FanWindowProfile V)
    (reserve : IncidenceReserve V)
    {carrier : V}
    (member : carrier ∈
      (profile (base := base) (object := object) (baseline := baseline)
        (center := center) fanProfile reserve).declaredCarrierSupport) :
    object.graph.Reachable center carrier := by
  letI : DecidableEq V := object.input.vertices.decEq
  apply Core.FiniteWeightedSelection.Profile.declaredCarrierSupport_induction
    (profile (base := base) (object := object) (baseline := baseline)
      (center := center) fanProfile reserve)
    (fun carrier => object.graph.Reachable center carrier) ?_ ?_ member
  · intro baseCarrier baseMember
    change baseCarrier ∈ insert center
      ((HighCenterPort.ports object center).orderedValues.map
        (HighCenterPort.endpoint object center)).toFinset at baseMember
    rw [Finset.mem_insert] at baseMember
    rcases baseMember with equal | closedMember
    · subst baseCarrier
      exact SimpleGraph.Reachable.rfl
    · rw [List.mem_toFinset] at closedMember
      rcases List.mem_map.mp closedMember with
        ⟨port, _portMem, equal⟩
      subst baseCarrier
      exact (HighCenterPort.endpoint_adjacent object center port).reachable
  · intro incidence itemCarrier itemMember
    change itemCarrier ∈ ({incidence.1.1,
      HybridFanIncidence.other (object := object) (center := center)
        fanProfile incidence.1 incidence.2} : Finset V) at itemMember
    simp only [Finset.mem_insert, Finset.mem_singleton] at itemMember
    rcases itemMember with equal | equal
    · subst itemCarrier
      exact incidence.1.property.1.reachable
    · subst itemCarrier
      exact incidence.1.property.1.reachable.trans
        (HybridFanIncidence.other_adjacent (object := object)
          (center := center) fanProfile incidence.1 incidence.2).reachable

namespace Candidate

variable (fanProfile : FanClosedPort.FanWindowProfile V)
  (reserve : IncidenceReserve V)

theorem contains_every_window
    (candidate : Candidate (base := base) (object := object)
      (baseline := baseline) (center := center) fanProfile reserve)
    {incidence : Incidence (object := object) (center := center) fanProfile}
    (window : HybridFanIncidence.incidenceKind (object := object)
      (center := center) fanProfile incidence = .window) :
    incidence ∈ candidate.1 :=
  (profile (base := base) (object := object) (baseline := baseline)
    (center := center) fanProfile reserve).mandatory_mem candidate window

theorem selected_reserve_free
    (candidate : Candidate (base := base) (object := object)
      (baseline := baseline) (center := center) fanProfile reserve)
    {incidence : Incidence (object := object) (center := center) fanProfile}
    (selected : incidence ∈ candidate.1) :
    ¬reserve.Used (HybridFanIncidence.carrier (object := object)
      (center := center) fanProfile incidence) :=
  (profile (base := base) (object := object) (baseline := baseline)
    (center := center) fanProfile reserve).selected_not_forbidden
      candidate selected

theorem nonWindow_payment
    (candidate : Candidate (base := base) (object := object)
      (baseline := baseline) (center := center) fanProfile reserve) :
    HybridFanIncidence.remainingNonWindowDemand
        (base := base) (object := object) (baseline := baseline)
        (center := center) fanProfile ≤
      ∑ incidence ∈ candidate.1,
        if HybridFanIncidence.incidenceKind (object := object)
            (center := center) fanProfile incidence = .nonWindow
          then 2 else 0 :=
  (profile (base := base) (object := object) (baseline := baseline)
    (center := center) fanProfile reserve).payment candidate

theorem center_mem_support
    (candidate : Candidate (base := base) (object := object)
      (baseline := baseline) (center := center) fanProfile reserve) :
    center ∈ (profile (base := base) (object := object)
      (baseline := baseline) (center := center) fanProfile reserve
      ).carrierSupport candidate := by
  apply (profile (base := base) (object := object) (baseline := baseline)
    (center := center) fanProfile reserve).baseSupport_subset
  simp [profile, baseSupport]

end Candidate

end StructuralExhaustion.Graph.HybridFanCandidate
