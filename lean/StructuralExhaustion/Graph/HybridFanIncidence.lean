import Mathlib.Tactic
import StructuralExhaustion.CT14.Automation
import StructuralExhaustion.Graph.FanClosedPortMass
import StructuralExhaustion.Routes.CT14ToCT14

namespace StructuralExhaustion.Graph.HybridFanIncidence

open StructuralExhaustion

universe u

/-!
# CT14 refinement by actual cubic-closed incidences

Each cubic-closed neighbour has degree three and is adjacent to the centre,
so deleting the centre from its declared neighbour list leaves exactly two
actual incidences.  The executable universe is therefore the product of the
semantic cubic-closed subtype with `Bool`; it never materializes a
closed-neighbour-by-all-vertices table.

Four-cycle avoidance proves that the non-centre endpoints of distinct
incidences are pairwise distinct.  CT14 then partitions the exact incidence
universe into window and non-window labels and accounts for one half-credit
(two quarter-units) per incidence.
-/

variable {base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
variable {object : FiniteObject V} {baseline : base.problem.Baseline object}
variable {center : V} (centerHigh : 4 ≤ object.degree center)
variable (deletionCritical : ∀ dart : object.graph.Dart,
  object.degree dart.fst = 3 ∨ object.degree dart.snd = 3)

abbrev ClosedMember (profile : FanClosedPort.FanWindowProfile V) :=
  {vertex : V // FanClosedPortMass.CubicClosedNeighbor
    (object := object) (center := center) profile vertex}

@[implicit_reducible]
def closedMembers (profile : FanClosedPort.FanWindowProfile V) :
    FinEnum (ClosedMember (object := object) (center := center) profile) :=
  FanClosedPortMass.cubicClosedNeighbors
    (object := object) (center := center) profile

/-- The literal two-entry list obtained by deleting the centre from a
cubic-closed member's declared neighbour list. -/
def otherVertices (profile : FanClosedPort.FanWindowProfile V)
    (member : ClosedMember (object := object) (center := center) profile) :
    List V := by
  letI : DecidableEq V := object.input.vertices.decEq
  exact (object.input.orderedNeighbors member.1).values.erase center

theorem otherVertices_length (profile : FanClosedPort.FanWindowProfile V)
    (member : ClosedMember (object := object) (center := center) profile) :
    (otherVertices (object := object) (center := center) profile member).length = 2 := by
  letI : FinEnum V := object.input.vertices
  letI : DecidableEq V := object.input.vertices.decEq
  letI : DecidableRel object.graph.Adj := object.input.decideAdj
  rw [otherVertices, List.length_erase_of_mem]
  · rw [object.input.orderedNeighbors_length]
    have cubic := member.property.2.1
    change object.graph.degree member.1 = 3 at cubic
    rw [cubic]
  · exact (object.input.mem_orderedNeighbors_iff member.1 center).2
      member.property.1.symm

def firstOther (profile : FanClosedPort.FanWindowProfile V)
    (member : ClosedMember (object := object) (center := center) profile) : V :=
  (otherVertices (object := object) (center := center) profile member)[0]'(by
    rw [otherVertices_length (object := object) (center := center) profile member]
    decide)

def secondOther (profile : FanClosedPort.FanWindowProfile V)
    (member : ClosedMember (object := object) (center := center) profile) : V :=
  (otherVertices (object := object) (center := center) profile member)[1]'(by
    rw [otherVertices_length (object := object) (center := center) profile member]
    decide)

def other (profile : FanClosedPort.FanWindowProfile V)
    (member : ClosedMember (object := object) (center := center) profile)
    (side : Bool) : V :=
  if side then secondOther (object := object) (center := center) profile member
  else firstOther (object := object) (center := center) profile member

/-- The unique literal port whose endpoint is a cubic-closed member. -/
noncomputable def memberPort
    (profile : FanClosedPort.FanWindowProfile V)
    (member : ClosedMember (object := object) (center := center) profile) :
    HighCenterPort.Port object center :=
  (HighCenterPort.neighborEquiv object center).symm
    ⟨member.1, member.2.1⟩

theorem endpoint_memberPort
    (profile : FanClosedPort.FanWindowProfile V)
    (member : ClosedMember (object := object) (center := center) profile) :
    HighCenterPort.endpoint object center
        (memberPort (object := object) (center := center) profile member) =
      member.1 := by
  exact congrArg Subtype.val
    ((HighCenterPort.neighborEquiv object center).apply_symm_apply
      ⟨member.1, member.2.1⟩)

theorem memberPort_injective
    (profile : FanClosedPort.FanWindowProfile V) :
    Function.Injective
      (memberPort (object := object) (center := center) profile) := by
  intro left right equal
  apply Subtype.ext
  rw [← endpoint_memberPort (object := object) (center := center) profile left,
    ← endpoint_memberPort (object := object) (center := center) profile right,
    equal]

/-- The `Bool` incidence coordinate is exactly the corresponding coordinate
in the literal two-shoulder port list. -/
theorem other_eq_portShoulder
    (profile : FanClosedPort.FanWindowProfile V)
    (member : ClosedMember (object := object) (center := center) profile)
    (side : Bool) :
    other (object := object) (center := center) profile member side =
      if side then
        HighCenterPort.secondShoulder object center centerHigh
          deletionCritical
          (memberPort (object := object) (center := center) profile member)
      else
        HighCenterPort.firstShoulder object center centerHigh
          deletionCritical
          (memberPort (object := object) (center := center) profile member) := by
  have listsEqual :
      otherVertices (object := object) (center := center) profile member =
        HighCenterPort.shoulderVertices object center
          (memberPort (object := object) (center := center) profile member) := by
    unfold otherVertices HighCenterPort.shoulderVertices
    rw [endpoint_memberPort (object := object) (center := center) profile member]
  cases side
  · simp only [other, Bool.false_eq_true, if_false]
    unfold firstOther HighCenterPort.firstShoulder
    simpa only [listsEqual]
  · simp only [other, if_true]
    unfold secondOther HighCenterPort.secondShoulder
    simpa only [listsEqual]

theorem firstOther_mem (profile : FanClosedPort.FanWindowProfile V)
    (member : ClosedMember (object := object) (center := center) profile) :
    firstOther (object := object) (center := center) profile member ∈
      otherVertices (object := object) (center := center) profile member := by
  unfold firstOther
  exact List.get_mem _ _

theorem secondOther_mem (profile : FanClosedPort.FanWindowProfile V)
    (member : ClosedMember (object := object) (center := center) profile) :
    secondOther (object := object) (center := center) profile member ∈
      otherVertices (object := object) (center := center) profile member := by
  unfold secondOther
  exact List.get_mem _ _

theorem other_mem (profile : FanClosedPort.FanWindowProfile V)
    (member : ClosedMember (object := object) (center := center) profile)
    (side : Bool) :
    other (object := object) (center := center) profile member side ∈
      otherVertices (object := object) (center := center) profile member := by
  cases side
  · exact firstOther_mem (object := object) (center := center) profile member
  · exact secondOther_mem (object := object) (center := center) profile member

theorem other_adjacent (profile : FanClosedPort.FanWindowProfile V)
    (member : ClosedMember (object := object) (center := center) profile)
    (side : Bool) :
    object.graph.Adj member.1
      (other (object := object) (center := center) profile member side) := by
  letI : DecidableEq V := object.input.vertices.decEq
  apply (object.input.mem_orderedNeighbors_iff member.1 _).1
  exact List.mem_of_mem_erase
    (other_mem (object := object) (center := center) profile member side)

theorem other_ne_center (profile : FanClosedPort.FanWindowProfile V)
    (member : ClosedMember (object := object) (center := center) profile)
    (side : Bool) :
    other (object := object) (center := center) profile member side ≠ center := by
  letI : DecidableEq V := object.input.vertices.decEq
  have memberOfErase :=
    other_mem (object := object) (center := center) profile member side
  have nodup := (object.input.orderedNeighbors member.1).nodup
  unfold otherVertices at memberOfErase
  exact (nodup.mem_erase_iff.mp memberOfErase).1

theorem firstOther_ne_secondOther (profile : FanClosedPort.FanWindowProfile V)
    (member : ClosedMember (object := object) (center := center) profile) :
    firstOther (object := object) (center := center) profile member ≠
      secondOther (object := object) (center := center) profile member := by
  letI : DecidableEq V := object.input.vertices.decEq
  intro equal
  have nodup : (otherVertices (object := object) (center := center)
      profile member).Nodup := by
    unfold otherVertices
    exact (object.input.orderedNeighbors member.1).nodup.erase _
  have indexEq := nodup.injective_get equal
  have valueEq := congrArg Fin.val indexEq
  norm_num at valueEq

abbrev Incidence (profile : FanClosedPort.FanWindowProfile V) :=
  ClosedMember (object := object) (center := center) profile × Bool

@[implicit_reducible]
def incidences (profile : FanClosedPort.FanWindowProfile V) :
    FinEnum (Incidence (object := object) (center := center) profile) :=
  Core.Enumeration.prod
    (closedMembers (object := object) (center := center) profile)
    Core.Enumeration.bool

def carrier (profile : FanClosedPort.FanWindowProfile V)
    (incidence : Incidence (object := object) (center := center) profile) :
    FanClosedPort.LocalCarrier V :=
  (incidence.1.1, other (object := object) (center := center)
    profile incidence.1 incidence.2)

theorem carrier_adjacent (profile : FanClosedPort.FanWindowProfile V)
    (incidence : Incidence (object := object) (center := center) profile) :
    object.graph.Adj (carrier (object := object) (center := center)
      profile incidence).1 (carrier (object := object) (center := center)
        profile incidence).2 :=
  other_adjacent (object := object) (center := center) profile
    incidence.1 incidence.2

theorem carrier_assigned (profile : FanClosedPort.FanWindowProfile V)
    (incidence : Incidence (object := object) (center := center) profile) :
    profile.Assigned
      (carrier (object := object) (center := center) profile incidence) :=
  incidence.1.property.2.2.2 _
    (carrier_adjacent (object := object) (center := center) profile incidence)
    (other_ne_center (object := object) (center := center) profile
      incidence.1 incidence.2)

def incidenceKind (profile : FanClosedPort.FanWindowProfile V)
    (incidence : Incidence (object := object) (center := center) profile) :
    FanClosedPort.IncidenceKind :=
  @ite FanClosedPort.IncidenceKind
    (profile.WindowSide (carrier (object := object) (center := center)
      profile incidence).2)
    (profile.windowDecidable (carrier (object := object) (center := center)
      profile incidence).2)
    .window .nonWindow

theorem incidenceKind_exhaustive (profile : FanClosedPort.FanWindowProfile V)
    (incidence : Incidence (object := object) (center := center) profile) :
    incidenceKind (object := object) (center := center) profile incidence = .window ∨
      incidenceKind (object := object) (center := center) profile incidence =
        .nonWindow := by
  unfold incidenceKind
  split <;> simp

theorem incidenceKind_eq_nonWindow_iff
    (profile : FanClosedPort.FanWindowProfile V)
    (incidence : Incidence (object := object) (center := center) profile) :
    incidenceKind (object := object) (center := center) profile incidence =
        .nonWindow ↔
      ¬profile.WindowSide
        (other (object := object) (center := center)
          profile incidence.1 incidence.2) := by
  unfold incidenceKind carrier
  split <;> simp_all

/-- In a four-cycle-free graph, two distinct cubic-closed incidences cannot
reuse a non-centre endpoint. -/
theorem other_injective (profile : FanClosedPort.FanWindowProfile V)
    (fourFree : ¬HasCycleWithLength object.graph HighCenterStructure.FourLength) :
    Function.Injective (fun incidence : Incidence (object := object)
      (center := center) profile =>
        other (object := object) (center := center) profile incidence.1 incidence.2) := by
  intro left right sameOther
  rcases left with ⟨leftMember, leftSide⟩
  rcases right with ⟨rightMember, rightSide⟩
  by_cases sameMember : leftMember = rightMember
  · subst rightMember
    cases leftSide <;> cases rightSide
    · rfl
    · exact (firstOther_ne_secondOther (object := object) (center := center)
        profile leftMember sameOther).elim
    · exact (firstOther_ne_secondOther (object := object) (center := center)
        profile leftMember sameOther.symm).elim
    · rfl
  · have endpointNe : leftMember.1 ≠ rightMember.1 := by
      intro equal
      exact sameMember (Subtype.ext equal)
    exfalso
    apply fourFree
    exact ⟨HighCenterStructure.squareCycle
      leftMember.property.1
      (other_adjacent (object := object) (center := center) profile
        leftMember leftSide)
      (by simpa [sameOther] using
        (other_adjacent (object := object) (center := center) profile
          rightMember rightSide).symm)
      rightMember.property.1.symm
      (other_ne_center (object := object) (center := center) profile
        leftMember leftSide).symm endpointNe⟩

theorem incidence_card (profile : FanClosedPort.FanWindowProfile V) :
    (incidences (object := object) (center := center) profile).card =
      2 * (closedMembers (object := object) (center := center) profile).card := by
  letI : FinEnum (ClosedMember (object := object) (center := center) profile) :=
    closedMembers (object := object) (center := center) profile
  letI : FinEnum (Incidence (object := object) (center := center) profile) :=
    incidences (object := object) (center := center) profile
  rw [FinEnum.card_eq_fintypeCard]
  change Fintype.card (ClosedMember (object := object) (center := center)
    profile × Bool) = _
  rw [Fintype.card_prod, Fintype.card_bool,
    FinEnum.card_eq_fintypeCard]
  omega

theorem incidence_card_le_twice_vertices
    (profile : FanClosedPort.FanWindowProfile V) :
    (incidences (object := object) (center := center) profile).card ≤
      2 * object.input.vertices.card := by
  rw [incidence_card (object := object) (center := center)]
  exact Nat.mul_le_mul_left 2
    (FanClosedPortMass.cubicClosed_card_le_vertices
      (object := object) (center := center) profile)

/-! ## CT14 incidence-capacity refinement -/

def capability (profile : FanClosedPort.FanWindowProfile V) :
    CT14.Capability base.problem where
  Member := Incidence (object := object) (center := center) profile
  members := incidences (object := object) (center := center) profile
  Label := FanClosedPort.IncidenceKind
  labelDecidableEq := inferInstance
  memberLowerMass := fun _ctx _incidence => 2
  memberCapacity := fun _ctx _incidence => some 2
  memberLabel := fun _ctx incidence =>
    some (incidenceKind (object := object) (center := center) profile incidence)

def context (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit))
    (object : FiniteObject V) (baseline : base.problem.Baseline object) :
    Core.BranchContext base.problem :=
  ⟨object, baseline, ()⟩

def sourceResidual (profile : FanClosedPort.FanWindowProfile V)
    (first second : FanClosedPort.OpenPort centerHigh deletionCritical)
    (assigned : FanClosedPort.AssignedPair centerHigh deletionCritical profile
      first second) :
    CT14.CapacityResidual
      (FanClosedPortMass.capability (base := base) (object := object)
        (center := center) profile)
      (FanClosedPortMass.context base object baseline) :=
  CT14.ExecutionResult.capacityResidual
    (FanClosedPortMass.run (base := base) (baseline := baseline) centerHigh
      deletionCritical profile first second assigned)
    (FanClosedPortMass.run_terminal_capacity (base := base) (baseline := baseline)
      centerHigh deletionCritical profile first second assigned)

/-- Framework-owned CT14 refinement profile. -/
abbrev transition (profile : FanClosedPort.FanWindowProfile V) :=
  Routes.CT14ToCT14.transition
    (sourceCapability := FanClosedPortMass.capability (base := base)
      (object := object) (center := center) profile)
    (ctx := FanClosedPortMass.context base object baseline)
    (capability (base := base) (object := object) (center := center) profile)

/-- Execute the second CT14 pass from the complete first transition ledger. -/
def executionStage (profile : FanClosedPort.FanWindowProfile V)
    (first second : FanClosedPort.OpenPort centerHigh deletionCritical)
    (assigned : FanClosedPort.AssignedPair centerHigh deletionCritical profile
      first second) :=
  Routes.CT14ToCT14.advance
    (capability (base := base) (object := object) (center := center) profile)
    (fun _previous => sourceResidual (base := base) (baseline := baseline)
      centerHigh deletionCritical profile first second assigned)
    (FanClosedPortMass.ledgerStage (base := base) (baseline := baseline)
      centerHigh deletionCritical profile first second assigned)

/-- Accumulated second CT14 ledger, retaining the entire CT5→CT14 prefix. -/
def ledgerStage (profile : FanClosedPort.FanWindowProfile V)
    (first second : FanClosedPort.OpenPort centerHigh deletionCritical)
    (assigned : FanClosedPort.AssignedPair centerHigh deletionCritical profile
      first second) :=
  (executionStage (base := base) (baseline := baseline) centerHigh
    deletionCritical profile first second assigned).ledgerStage

def routedInput (profile : FanClosedPort.FanWindowProfile V)
    (first second : FanClosedPort.OpenPort centerHigh deletionCritical)
    (assigned : FanClosedPort.AssignedPair centerHigh deletionCritical profile
      first second) :=
  let transition := transition (base := base) (object := object)
    (baseline := baseline) (center := center) profile
  let execution := transition.onLedger (fun _previous =>
    sourceResidual (base := base) (baseline := baseline) centerHigh
      deletionCritical profile first second assigned)
  let source := FanClosedPortMass.ledgerStage (base := base)
    (baseline := baseline) centerHigh deletionCritical profile first second assigned
  execution.trigger source ()

def run (profile : FanClosedPort.FanWindowProfile V)
    (first second : FanClosedPort.OpenPort centerHigh deletionCritical)
    (assigned : FanClosedPort.AssignedPair centerHigh deletionCritical profile
      first second) :
    CT14.ExecutionResult
      (capability (base := base) (object := object) (center := center) profile)
      (context base object baseline) :=
  (executionStage (base := base) (baseline := baseline) centerHigh
    deletionCritical profile first second assigned).targetResult

theorem lowerMass_eq (profile : FanClosedPort.FanWindowProfile V) :
    CT14.lowerMass
      (capability (base := base) (object := object) (center := center) profile)
      (context base object baseline) =
      2 * (incidences (object := object) (center := center) profile).card := by
  change ((incidences (object := object) (center := center) profile
    ).orderedValues.map (fun _incidence => 2)).sum = _
  simp [Nat.mul_comm]

theorem upperCapacity_eq (profile : FanClosedPort.FanWindowProfile V) :
    CT14.upperCapacity
      (capability (base := base) (object := object) (center := center) profile)
      (context base object baseline) =
      2 * (incidences (object := object) (center := center) profile).card := by
  change ((incidences (object := object) (center := center) profile
    ).orderedValues.map (fun _incidence => 2)).sum = _
  simp [Nat.mul_comm]

theorem multiplicity_partition (profile : FanClosedPort.FanWindowProfile V) :
    CT14.multiplicity
        (capability (base := base) (object := object) (center := center) profile)
        (context base object baseline) .window +
      CT14.multiplicity
        (capability (base := base) (object := object) (center := center) profile)
        (context base object baseline) .nonWindow =
      (incidences (object := object) (center := center) profile).card := by
  apply CT14.multiplicity_add_eq_card_of_binary_labels
    (capability (base := base) (object := object) (center := center) profile)
    (context base object baseline) .window .nonWindow
      (show (FanClosedPort.IncidenceKind.window :
        FanClosedPort.IncidenceKind) ≠ .nonWindow by decide)
  intro incidence
  rcases incidenceKind_exhaustive (object := object) (center := center)
    profile incidence with window | nonWindow
  · left; simp [capability, window]
  · right; simp [capability, nonWindow]

theorem run_terminal_capacity (profile : FanClosedPort.FanWindowProfile V)
    (first second : FanClosedPort.OpenPort centerHigh deletionCritical)
    (assigned : FanClosedPort.AssignedPair centerHigh deletionCritical profile
      first second) :
    (run (base := base) (baseline := baseline) centerHigh deletionCritical
      profile first second assigned).terminal = .capacity := by
  change (CT14.run
    (capability (base := base) (object := object) (center := center) profile)
    (context base object baseline)
    (routedInput (base := base) (baseline := baseline) centerHigh
      deletionCritical profile first second assigned)).terminal = .capacity
  apply CT14.run_terminal_capacity_of_complete
  · intro incidence; exact ⟨2, rfl⟩
  · intro incidence
    exact ⟨incidenceKind (object := object) (center := center) profile incidence,
      rfl⟩
  · rw [lowerMass_eq (base := base) (baseline := baseline)
      (center := center) profile,
      upperCapacity_eq (base := base) (baseline := baseline)
        (center := center) profile]

theorem run_trace_capacity (profile : FanClosedPort.FanWindowProfile V)
    (first second : FanClosedPort.OpenPort centerHigh deletionCritical)
    (assigned : FanClosedPort.AssignedPair centerHigh deletionCritical profile
      first second) :
    (run (base := base) (baseline := baseline) centerHigh deletionCritical
      profile first second assigned).trace =
      [.entry, .lowerMass, .memberScan, .upperCapacity, .comparison,
        .capacityTerminal] := by
  change (CT14.run
    (capability (base := base) (object := object) (center := center) profile)
    (context base object baseline)
    (routedInput (base := base) (baseline := baseline) centerHigh
      deletionCritical profile first second assigned)).trace = _
  apply CT14.run_trace_capacity_of_complete
  · intro incidence; exact ⟨2, rfl⟩
  · intro incidence
    exact ⟨incidenceKind (object := object) (center := center) profile incidence,
      rfl⟩
  · rw [lowerMass_eq (base := base) (baseline := baseline)
      (center := center) profile,
      upperCapacity_eq (base := base) (baseline := baseline)
        (center := center) profile]

/-! ## Exact quarter-unit arithmetic -/

def totalQuarterCredit (profile : FanClosedPort.FanWindowProfile V) : Nat :=
  2 * (incidences (object := object) (center := center) profile).card

def windowQuarterCredit (profile : FanClosedPort.FanWindowProfile V) : Nat :=
  2 * CT14.multiplicity
    (capability (base := base) (object := object) (center := center) profile)
    (context base object baseline) .window

def nonWindowQuarterCredit (profile : FanClosedPort.FanWindowProfile V) : Nat :=
  2 * CT14.multiplicity
    (capability (base := base) (object := object) (center := center) profile)
    (context base object baseline) .nonWindow

theorem totalQuarterCredit_eq_four_mul_closed
    (profile : FanClosedPort.FanWindowProfile V) :
    totalQuarterCredit (object := object) (center := center) profile =
      4 * (closedMembers (object := object) (center := center) profile).card := by
  rw [totalQuarterCredit, incidence_card (object := object) (center := center)]
  omega

theorem window_add_nonWindow_credit
    (profile : FanClosedPort.FanWindowProfile V) :
    windowQuarterCredit (base := base) (object := object) (baseline := baseline)
        (center := center) profile +
      nonWindowQuarterCredit (base := base) (object := object)
        (baseline := baseline) (center := center) profile =
      totalQuarterCredit (object := object) (center := center) profile := by
  unfold windowQuarterCredit nonWindowQuarterCredit totalQuarterCredit
  have partition := multiplicity_partition (base := base) (baseline := baseline)
    (center := center) profile
  omega

theorem total_credit_pays_deficit_with_three_slack
    (profile : FanClosedPort.FanWindowProfile V)
    (degreeLeEight : object.degree center ≤ 8) :
    (3 : Int) ≤
      (totalQuarterCredit (object := object) (center := center) profile : Int) -
        FanClosedPortMass.deficitNumerator (object.degree center)
          (closedMembers (object := object) (center := center) profile).card := by
  rw [totalQuarterCredit_eq_four_mul_closed
    (object := object) (center := center) profile]
  unfold FanClosedPortMass.deficitNumerator
  omega

def remainingNonWindowDemand (profile : FanClosedPort.FanWindowProfile V) : Int :=
  max 0 (FanClosedPortMass.deficitNumerator (object.degree center)
    (closedMembers (object := object) (center := center) profile).card -
      (windowQuarterCredit (base := base) (object := object)
        (baseline := baseline) (center := center) profile : Int))

theorem nonWindow_credit_pays_remaining
    (profile : FanClosedPort.FanWindowProfile V)
    (degreeLeEight : object.degree center ≤ 8) :
    remainingNonWindowDemand (base := base) (object := object)
        (baseline := baseline) (center := center) profile ≤
      (nonWindowQuarterCredit (base := base) (object := object)
        (baseline := baseline) (center := center) profile : Int) := by
  have totalPays := total_credit_pays_deficit_with_three_slack
    (object := object) (center := center) profile degreeLeEight
  have partition := window_add_nonWindow_credit
    (base := base) (object := object) (baseline := baseline)
    (center := center) profile
  unfold remainingNonWindowDemand
  by_cases nonpositive :
      FanClosedPortMass.deficitNumerator (object.degree center)
          (closedMembers (object := object) (center := center) profile).card -
        (windowQuarterCredit (base := base) (object := object)
          (baseline := baseline) (center := center) profile : Int) ≤ 0
  · rw [max_eq_left nonpositive]
    exact Int.natCast_nonneg _
  · have positive : (0 : Int) ≤
        FanClosedPortMass.deficitNumerator (object.degree center)
            (closedMembers (object := object) (center := center) profile).card -
          (windowQuarterCredit (base := base) (object := object)
            (baseline := baseline) (center := center) profile : Int) := by
      omega
    rw [max_eq_right positive]
    have partitionInt :
        (totalQuarterCredit (object := object) (center := center) profile : Int) =
          (windowQuarterCredit (base := base) (object := object)
              (baseline := baseline) (center := center) profile : Int) +
            (nonWindowQuarterCredit (base := base) (object := object)
              (baseline := baseline) (center := center) profile : Int) := by
      exact_mod_cast partition.symm
    omega

/-- Conservative audit: constructing the semantic closed subtype may inspect
all vertices for each candidate; every incidence pass is only linear in the
resulting two-per-member universe. -/
def checks : Nat :=
  4 * object.input.vertices.card ^ 2 +
    20 * object.input.vertices.card + 1

structure VerifiedStage (profile : FanClosedPort.FanWindowProfile V)
    (first second : FanClosedPort.OpenPort centerHigh deletionCritical)
    (pair : FanClosedPort.CompatiblePair centerHigh deletionCritical first second)
    (assigned : FanClosedPort.AssignedPair centerHigh deletionCritical profile
      first second)
    (fourFree : ¬HasCycleWithLength object.graph HighCenterStructure.FourLength)
    (degreeLeEight : object.degree center ≤ 8) : Prop where
  previous : FanClosedPortMass.VerifiedStage
    (base := base) (baseline := baseline) centerHigh deletionCritical profile
    first second pair assigned
  transitionProfileId :
    (transition (base := base) (object := object) (baseline := baseline)
      (center := center) profile).profileId =
      "CT14.residual.capacity->CT14"
  terminal : (run (base := base) (baseline := baseline) centerHigh
    deletionCritical profile first second assigned).terminal = .capacity
  trace : (run (base := base) (baseline := baseline) centerHigh
    deletionCritical profile first second assigned).trace =
    [.entry, .lowerMass, .memberScan, .upperCapacity, .comparison,
      .capacityTerminal]
  incidenceCardExact : (incidences (object := object) (center := center) profile).card =
    2 * (closedMembers (object := object) (center := center) profile).card
  memoryLinear : (incidences (object := object) (center := center) profile).card ≤
    2 * object.input.vertices.card
  endpointDisjoint : Function.Injective (fun incidence :
    Incidence (object := object) (center := center) profile =>
      other (object := object) (center := center) profile incidence.1 incidence.2)
  partition : CT14.multiplicity
      (capability (base := base) (object := object) (center := center) profile)
      (context base object baseline) .window +
    CT14.multiplicity
      (capability (base := base) (object := object) (center := center) profile)
      (context base object baseline) .nonWindow =
    (incidences (object := object) (center := center) profile).card
  creditPays : (3 : Int) ≤
    (totalQuarterCredit (object := object) (center := center) profile : Int) -
      FanClosedPortMass.deficitNumerator (object.degree center)
        (closedMembers (object := object) (center := center) profile).card
  reservePays : remainingNonWindowDemand (base := base) (object := object)
      (baseline := baseline) (center := center) profile ≤
    (nonWindowQuarterCredit (base := base) (object := object)
      (baseline := baseline) (center := center) profile : Int)
  total : ∃ result : CT14.ExecutionResult
      (capability (base := base) (object := object) (center := center) profile)
      (context base object baseline),
    result.outcome.Valid ∧ @CT14.Graph.ValidTrace base.problem
      (capability (base := base) (object := object) (center := center) profile)
      (context base object baseline) result.trace
  polynomial : checks (object := object) ≤
    4 * object.input.vertices.card ^ 2 +
      20 * object.input.vertices.card + 1

/-- Semantic local ledger entry extracted from the CT14 execution.  This is
the reusable graph-level form of a local B1-style statement: the literal
incidences are endpoint-disjoint, split exactly into the two declared pools,
and their total and non-window capacities pay the corresponding demands. -/
structure LocalLedgerEntry (profile : FanClosedPort.FanWindowProfile V)
    (first second : FanClosedPort.OpenPort centerHigh deletionCritical)
    (assigned : FanClosedPort.AssignedPair centerHigh deletionCritical profile
      first second) : Prop where
  terminal : (run (base := base) (baseline := baseline) centerHigh
    deletionCritical profile first second assigned).terminal = .capacity
  incidenceCardExact :
    (incidences (object := object) (center := center) profile).card =
      2 * (closedMembers (object := object) (center := center) profile).card
  endpointDisjoint : Function.Injective (fun incidence :
    Incidence (object := object) (center := center) profile =>
      other (object := object) (center := center) profile incidence.1 incidence.2)
  partition : CT14.multiplicity
      (capability (base := base) (object := object) (center := center) profile)
      (context base object baseline) .window +
    CT14.multiplicity
      (capability (base := base) (object := object) (center := center) profile)
      (context base object baseline) .nonWindow =
    (incidences (object := object) (center := center) profile).card
  totalCreditPays : (3 : Int) ≤
    (totalQuarterCredit (object := object) (center := center) profile : Int) -
      FanClosedPortMass.deficitNumerator (object.degree center)
        (closedMembers (object := object) (center := center) profile).card
  nonWindowCreditPays :
    remainingNonWindowDemand (base := base) (object := object)
        (baseline := baseline) (center := center) profile ≤
      (nonWindowQuarterCredit (base := base) (object := object)
        (baseline := baseline) (center := center) profile : Int)

/-- Construct the reusable local B1 ledger directly from its graph
hypotheses.  This theorem contains no proof-chain transport; applications
that need a CT14 execution use `VerifiedExecutionStage` instead. -/
def localLedgerEntry (profile : FanClosedPort.FanWindowProfile V)
    (first second : FanClosedPort.OpenPort centerHigh deletionCritical)
    (assigned : FanClosedPort.AssignedPair centerHigh deletionCritical profile
      first second)
    (fourFree : ¬HasCycleWithLength object.graph HighCenterStructure.FourLength)
    (degreeLeEight : object.degree center ≤ 8) :
    LocalLedgerEntry (base := base) (baseline := baseline) centerHigh
      deletionCritical profile first second assigned where
  terminal := run_terminal_capacity centerHigh deletionCritical profile first
    second assigned
  incidenceCardExact := incidence_card profile
  endpointDisjoint := other_injective profile fourFree
  partition := multiplicity_partition profile
  totalCreditPays :=
    total_credit_pays_deficit_with_three_slack profile degreeLeEight
  nonWindowCreditPays := nonWindow_credit_pays_remaining profile degreeLeEight

def verifiedStage (profile : FanClosedPort.FanWindowProfile V)
    (first second : FanClosedPort.OpenPort centerHigh deletionCritical)
    (pair : FanClosedPort.CompatiblePair centerHigh deletionCritical first second)
    (assigned : FanClosedPort.AssignedPair centerHigh deletionCritical profile
      first second)
    (fourFree : ¬HasCycleWithLength object.graph HighCenterStructure.FourLength)
    (degreeLeEight : object.degree center ≤ 8) :
    VerifiedStage (base := base) (baseline := baseline) centerHigh
      deletionCritical profile first second pair assigned fourFree degreeLeEight := by
  exact {
    previous := FanClosedPortMass.verifiedStage centerHigh deletionCritical
      profile first second pair assigned
    transitionProfileId := by rfl
    terminal := run_terminal_capacity centerHigh deletionCritical profile first
      second assigned
    trace := run_trace_capacity centerHigh deletionCritical profile first second
      assigned
    incidenceCardExact := incidence_card profile
    memoryLinear := incidence_card_le_twice_vertices profile
    endpointDisjoint := other_injective profile fourFree
    partition := multiplicity_partition profile
    creditPays := total_credit_pays_deficit_with_three_slack profile degreeLeEight
    reservePays := nonWindow_credit_pays_remaining profile degreeLeEight
    total := CT14.run_total
      (capability (base := base) (object := object) (center := center) profile)
      (context base object baseline)
      (routedInput (base := base) (baseline := baseline) centerHigh
        deletionCritical profile first second assigned)
    polynomial := by rfl
  }

/-- Hybrid semantics tied to the literal source and target CT14 executions of
an accumulated CT14→CT14 transition.  This is the reusable graph-layer
contract for proof chains; it never substitutes a detached rerun for either
execution. -/
structure VerifiedExecutionStage (profile : FanClosedPort.FanWindowProfile V)
    (first second : FanClosedPort.OpenPort centerHigh deletionCritical)
    (pair : FanClosedPort.CompatiblePair centerHigh deletionCritical first second)
    (assigned : FanClosedPort.AssignedPair centerHigh deletionCritical profile
      first second)
    (fourFree : ¬HasCycleWithLength object.graph HighCenterStructure.FourLength)
    (degreeLeEight : object.degree center ≤ 8)
    (sourceExecution : CT14.ExecutionResult
      (FanClosedPortMass.capability (base := base) (object := object)
        (center := center) profile)
      (FanClosedPortMass.context base object baseline))
    (targetExecution : CT14.ExecutionResult
      (capability (base := base) (object := object) (center := center) profile)
      (context base object baseline)) : Prop where
  previous : FanClosedPortMass.VerifiedExecutionStage
    (base := base) (baseline := baseline) centerHigh deletionCritical profile
    first second pair assigned sourceExecution
  transitionProfileId :
    (transition (base := base) (object := object) (baseline := baseline)
      (center := center) profile).profileId =
      "CT14.residual.capacity->CT14"
  executionExact : targetExecution = CT14.run
    (capability (base := base) (object := object) (center := center) profile)
    (context base object baseline) ⟨⟩
  terminal : targetExecution.terminal = .capacity
  trace : targetExecution.trace =
    [.entry, .lowerMass, .memberScan, .upperCapacity, .comparison,
      .capacityTerminal]
  incidenceCardExact :
    (incidences (object := object) (center := center) profile).card =
      2 * (closedMembers (object := object) (center := center) profile).card
  memoryLinear :
    (incidences (object := object) (center := center) profile).card ≤
      2 * object.input.vertices.card
  endpointDisjoint : Function.Injective (fun incidence :
    Incidence (object := object) (center := center) profile =>
      other (object := object) (center := center) profile incidence.1 incidence.2)
  partition : CT14.multiplicity
      (capability (base := base) (object := object) (center := center) profile)
      (context base object baseline) .window +
    CT14.multiplicity
      (capability (base := base) (object := object) (center := center) profile)
      (context base object baseline) .nonWindow =
    (incidences (object := object) (center := center) profile).card
  creditPays : (3 : Int) ≤
    (totalQuarterCredit (object := object) (center := center) profile : Int) -
      FanClosedPortMass.deficitNumerator (object.degree center)
        (closedMembers (object := object) (center := center) profile).card
  reservePays : remainingNonWindowDemand (base := base) (object := object)
      (baseline := baseline) (center := center) profile ≤
    (nonWindowQuarterCredit (base := base) (object := object)
      (baseline := baseline) (center := center) profile : Int)
  total : targetExecution.outcome.Valid ∧ @CT14.Graph.ValidTrace base.problem
    (capability (base := base) (object := object) (center := center) profile)
    (context base object baseline) targetExecution.trace
  polynomial : checks (object := object) ≤
    4 * object.input.vertices.card ^ 2 +
      20 * object.input.vertices.card + 1

/-- Build the execution-indexed hybrid certificate from the preceding literal
mass execution and the literal result produced by the CT14→CT14 route. -/
def verifiedExecutionStage (profile : FanClosedPort.FanWindowProfile V)
    (first second : FanClosedPort.OpenPort centerHigh deletionCritical)
    (pair : FanClosedPort.CompatiblePair centerHigh deletionCritical first second)
    (assigned : FanClosedPort.AssignedPair centerHigh deletionCritical profile
      first second)
    (fourFree : ¬HasCycleWithLength object.graph HighCenterStructure.FourLength)
    (degreeLeEight : object.degree center ≤ 8)
    (sourceExecution : CT14.ExecutionResult
      (FanClosedPortMass.capability (base := base) (object := object)
        (center := center) profile)
      (FanClosedPortMass.context base object baseline))
    (previous : FanClosedPortMass.VerifiedExecutionStage
      (base := base) (baseline := baseline) centerHigh deletionCritical profile
      first second pair assigned sourceExecution)
    (targetExecution : CT14.ExecutionResult
      (capability (base := base) (object := object) (center := center) profile)
      (context base object baseline))
    (executionExact : targetExecution = CT14.run
      (capability (base := base) (object := object) (center := center) profile)
      (context base object baseline) ⟨⟩) :
    VerifiedExecutionStage (base := base) (baseline := baseline) centerHigh
      deletionCritical profile first second pair assigned fourFree degreeLeEight
      sourceExecution targetExecution := by
  let semantic := verifiedStage (base := base) (baseline := baseline) centerHigh
    deletionCritical profile first second pair assigned fourFree degreeLeEight
  exact {
    previous := previous
    transitionProfileId := by rfl
    executionExact := executionExact
    terminal := by
      rw [executionExact]
      apply CT14.run_terminal_capacity_of_complete
      · intro incidence; exact ⟨2, rfl⟩
      · intro incidence
        exact ⟨incidenceKind (object := object) (center := center) profile incidence,
          rfl⟩
      · rw [lowerMass_eq (base := base) (baseline := baseline)
          (center := center) profile,
          upperCapacity_eq (base := base) (baseline := baseline)
            (center := center) profile]
    trace := by
      rw [executionExact]
      apply CT14.run_trace_capacity_of_complete
      · intro incidence; exact ⟨2, rfl⟩
      · intro incidence
        exact ⟨incidenceKind (object := object) (center := center) profile incidence,
          rfl⟩
      · rw [lowerMass_eq (base := base) (baseline := baseline)
          (center := center) profile,
          upperCapacity_eq (base := base) (baseline := baseline)
            (center := center) profile]
    incidenceCardExact := semantic.incidenceCardExact
    memoryLinear := semantic.memoryLinear
    endpointDisjoint := semantic.endpointDisjoint
    partition := semantic.partition
    creditPays := semantic.creditPays
    reservePays := semantic.reservePays
    total := by
      rw [executionExact]
      exact ⟨CT14.run_verified _ _ ⟨⟩, CT14.run_trace_valid _ _ ⟨⟩⟩
    polynomial := semantic.polynomial
  }

/-- Forget the execution bookkeeping while retaining every semantic fact used
by a local hybrid-ledger consumer. -/
def VerifiedStage.toLocalLedgerEntry
    (stage : VerifiedStage (base := base) (baseline := baseline) centerHigh
      deletionCritical profile first second pair assigned fourFree degreeLeEight) :
    LocalLedgerEntry (base := base) (baseline := baseline) centerHigh
      deletionCritical profile first second assigned where
  terminal := stage.terminal
  incidenceCardExact := stage.incidenceCardExact
  endpointDisjoint := stage.endpointDisjoint
  partition := stage.partition
  totalCreditPays := stage.creditPays
  nonWindowCreditPays := stage.reservePays

end StructuralExhaustion.Graph.HybridFanIncidence
