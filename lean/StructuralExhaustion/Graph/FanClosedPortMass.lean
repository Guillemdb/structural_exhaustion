import Mathlib.Tactic
import StructuralExhaustion.CT14.Automation
import StructuralExhaustion.Graph.AssignedFanCharge
import StructuralExhaustion.Graph.FanClosedPort
import StructuralExhaustion.Routes.CT5ToCT14

namespace StructuralExhaustion.Graph.FanClosedPortMass

open StructuralExhaustion

universe u

/-!
# CT14 mass of actual cubic-closed fan neighbours

The member universe is the executable subtype of declared vertices that are
adjacent to the centre, cubic, on the profile's remainder side, and whose
every non-centre incidence is assigned.  No claimed count is accepted.

The CT5-to-CT14 route consumes the actual charge residual produced by the
four-incidence compatible-pair stage.  CT14 scans the semantic subtype and
retains its exact cardinality as both lower mass and unit-label multiplicity.
-/

variable {base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)}
variable {object : FiniteObject V} {baseline : base.problem.Baseline object}
variable {center : V} (centerHigh : 4 ≤ object.degree center)
variable (deletionCritical : ∀ dart : object.graph.Dart,
  object.degree dart.fst = 3 ∨ object.degree dart.snd = 3)

/-- Literal cubic-closed-neighbour semantics of the assigned fan envelope. -/
def CubicClosedNeighbor (profile : FanClosedPort.FanWindowProfile V)
    (vertex : V) : Prop :=
  object.graph.Adj center vertex ∧
    object.degree vertex = 3 ∧
    profile.RemainderSide vertex ∧
    ∀ other, object.graph.Adj vertex other → other ≠ center →
      profile.Assigned (vertex, other)

def cubicClosedDecidable (profile : FanClosedPort.FanWindowProfile V) :
    ∀ vertex, Decidable (CubicClosedNeighbor (object := object)
      (center := center) profile vertex) := by
  intro vertex
  letI : FinEnum V := object.input.vertices
  letI : DecidableEq V := object.input.vertices.decEq
  letI : DecidableRel object.graph.Adj := object.input.decideAdj
  letI : DecidablePred profile.RemainderSide := profile.remainderDecidable
  letI : DecidablePred profile.Assigned := profile.assignedDecidable
  unfold CubicClosedNeighbor
  infer_instance

/-- Exact finite universe scanned by CT14. -/
@[implicit_reducible]
def cubicClosedNeighbors (profile : FanClosedPort.FanWindowProfile V) :
    FinEnum {vertex : V // CubicClosedNeighbor (object := object)
      (center := center) profile vertex} :=
  Core.Enumeration.subtype object.input.vertices
    (CubicClosedNeighbor (object := object) (center := center) profile)
    (cubicClosedDecidable (object := object) (center := center) profile)

@[implicit_reducible]
def assignedClosedPorts (profile : FanClosedPort.FanWindowProfile V) :
    FinEnum {port : HighCenterPort.Port object center //
      AssignedFanCharge.CubicClosed object center profile.Assigned port} :=
  Core.Enumeration.subtype (HighCenterPort.ports object center)
    (AssignedFanCharge.CubicClosed object center profile.Assigned)
    (AssignedFanCharge.cubicClosedDecidable object center profile.Assigned
      profile.assignedDecidable)

/-- If every fan neighbour lies on the remainder side, port-level assigned
closure and vertex-level cubic closure are the same literal finite set. -/
noncomputable def assignedClosedPortEquiv
    (profile : FanClosedPort.FanWindowProfile V)
    (allRemainder : ∀ port : HighCenterPort.Port object center,
      profile.RemainderSide (HighCenterPort.endpoint object center port)) :
    {port : HighCenterPort.Port object center //
      AssignedFanCharge.CubicClosed object center profile.Assigned port} ≃
    {vertex : V // CubicClosedNeighbor (object := object)
      (center := center) profile vertex} where
  toFun := fun port =>
    ⟨HighCenterPort.endpoint object center port.1,
      HighCenterPort.endpoint_adjacent object center port.1,
      HighCenterPort.endpoint_cubic object center centerHigh deletionCritical
        port.1,
      allRemainder port.1,
      port.2⟩
  invFun := fun member => by
    let neighbor : {vertex : V // object.graph.Adj center vertex} :=
      ⟨member.1, member.2.1⟩
    let port := (HighCenterPort.neighborEquiv object center).symm neighbor
    have endpointEq : HighCenterPort.endpoint object center port = member.1 := by
      exact congrArg Subtype.val
        ((HighCenterPort.neighborEquiv object center).apply_symm_apply neighbor)
    refine ⟨port, ?_⟩
    unfold AssignedFanCharge.CubicClosed
    rw [endpointEq]
    exact member.2.2.2.2
  left_inv := by
    intro port
    apply Subtype.ext
    change (HighCenterPort.neighborEquiv object center).symm
      ((HighCenterPort.neighborEquiv object center) port.1) = port.1
    exact (HighCenterPort.neighborEquiv object center).symm_apply_apply port.1
  right_inv := by
    intro member
    apply Subtype.ext
    let neighbor : {vertex : V // object.graph.Adj center vertex} :=
      ⟨member.1, member.2.1⟩
    change ((HighCenterPort.neighborEquiv object center)
      ((HighCenterPort.neighborEquiv object center).symm neighbor)).1 = member.1
    exact congrArg Subtype.val
      ((HighCenterPort.neighborEquiv object center).apply_symm_apply neighbor)

theorem cubicClosed_card_eq_assignedClosedPorts_card
    (centerHigh : 4 ≤ object.degree center)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3)
    (profile : FanClosedPort.FanWindowProfile V)
    (allRemainder : ∀ port : HighCenterPort.Port object center,
      profile.RemainderSide (HighCenterPort.endpoint object center port)) :
    (cubicClosedNeighbors (object := object) (center := center) profile).card =
      (assignedClosedPorts (object := object) (center := center) profile).card := by
  letI : FinEnum {port : HighCenterPort.Port object center //
      AssignedFanCharge.CubicClosed object center profile.Assigned port} :=
    assignedClosedPorts (object := object) (center := center) profile
  letI : FinEnum {vertex : V // CubicClosedNeighbor (object := object)
      (center := center) profile vertex} :=
    cubicClosedNeighbors (object := object) (center := center) profile
  rw [FinEnum.card_eq_fintypeCard, FinEnum.card_eq_fintypeCard]
  exact (Fintype.card_congr
    (assignedClosedPortEquiv centerHigh deletionCritical profile
      allRemainder)).symm

theorem fanClosed_is_cubicClosed (profile : FanClosedPort.FanWindowProfile V)
    (port : FanClosedPort.OpenPort centerHigh deletionCritical)
    (closed : FanClosedPort.FanClosed centerHigh deletionCritical profile port) :
    CubicClosedNeighbor (object := object) (center := center) profile
      (HighCenterPort.endpoint object center port.1) := by
  refine ⟨HighCenterPort.endpoint_adjacent object center port.1,
    HighCenterPort.endpoint_cubic object center centerHigh deletionCritical
      port.1, closed.1, ?_⟩
  intro other adjacent neCenter
  have member := HighCenterPort.mem_shoulders_of_adjacent_endpoint_of_ne_center
    object center port.1 adjacent neCenter
  rcases HighCenterPort.eq_firstShoulder_or_eq_secondShoulder_of_mem object
      center centerHigh deletionCritical port.1 member with first | second
  · subst other
    simpa [FanClosedPort.carrier, FanClosedPort.shoulder] using closed.2 false
  · subst other
    simpa [FanClosedPort.carrier, FanClosedPort.shoulder] using closed.2 true

def firstMember (profile : FanClosedPort.FanWindowProfile V)
    (first second : FanClosedPort.OpenPort centerHigh deletionCritical)
    (assigned : FanClosedPort.AssignedPair centerHigh deletionCritical profile
      first second) :
    {vertex : V // CubicClosedNeighbor (object := object) (center := center)
      profile vertex} :=
  ⟨HighCenterPort.endpoint object center first.1,
    fanClosed_is_cubicClosed centerHigh deletionCritical profile first
      (FanClosedPort.first_fanClosed centerHigh deletionCritical profile first
        second assigned)⟩

def secondMember (profile : FanClosedPort.FanWindowProfile V)
    (first second : FanClosedPort.OpenPort centerHigh deletionCritical)
    (assigned : FanClosedPort.AssignedPair centerHigh deletionCritical profile
      first second) :
    {vertex : V // CubicClosedNeighbor (object := object) (center := center)
      profile vertex} :=
  ⟨HighCenterPort.endpoint object center second.1,
    fanClosed_is_cubicClosed centerHigh deletionCritical profile second
      (FanClosedPort.second_fanClosed centerHigh deletionCritical profile first
        second assigned)⟩

def pairMember (profile : FanClosedPort.FanWindowProfile V)
    (first second : FanClosedPort.OpenPort centerHigh deletionCritical)
    (assigned : FanClosedPort.AssignedPair centerHigh deletionCritical profile
      first second) (side : Bool) :
    {vertex : V // CubicClosedNeighbor (object := object) (center := center)
      profile vertex} :=
  if side then secondMember centerHigh deletionCritical profile first second assigned
  else firstMember centerHigh deletionCritical profile first second assigned

theorem pairMember_injective (profile : FanClosedPort.FanWindowProfile V)
    (first second : FanClosedPort.OpenPort centerHigh deletionCritical)
    (pair : FanClosedPort.CompatiblePair centerHigh deletionCritical first second)
    (assigned : FanClosedPort.AssignedPair centerHigh deletionCritical profile
      first second) :
    Function.Injective
      (pairMember centerHigh deletionCritical profile first second assigned) := by
  intro left right equal
  cases left <;> cases right
  · rfl
  · exfalso
    exact FanClosedPort.endpoint_ne centerHigh deletionCritical first second pair
      (congrArg Subtype.val equal)
  · exfalso
    exact FanClosedPort.endpoint_ne centerHigh deletionCritical first second pair
      (congrArg Subtype.val equal).symm
  · rfl

theorem two_le_cubicClosed_card (profile : FanClosedPort.FanWindowProfile V)
    (first second : FanClosedPort.OpenPort centerHigh deletionCritical)
    (pair : FanClosedPort.CompatiblePair centerHigh deletionCritical first second)
    (assigned : FanClosedPort.AssignedPair centerHigh deletionCritical profile
      first second) :
    2 ≤ (cubicClosedNeighbors (object := object) (center := center) profile).card := by
  letI : FinEnum {vertex : V // CubicClosedNeighbor (object := object)
      (center := center) profile vertex} :=
    cubicClosedNeighbors (object := object) (center := center) profile
  have cardLe : Fintype.card Bool ≤ Fintype.card
      {vertex : V // CubicClosedNeighbor (object := object) (center := center)
        profile vertex} :=
    Fintype.card_le_of_injective
      (pairMember centerHigh deletionCritical profile first second assigned)
      (pairMember_injective centerHigh deletionCritical profile first second pair
        assigned)
  simpa [FinEnum.card_eq_fintypeCard] using cardLe

theorem cubicClosed_card_le_vertices
    (profile : FanClosedPort.FanWindowProfile V) :
    (cubicClosedNeighbors (object := object) (center := center) profile).card ≤
      object.input.vertices.card := by
  letI : FinEnum V := object.input.vertices
  letI : FinEnum {vertex : V // CubicClosedNeighbor (object := object)
      (center := center) profile vertex} :=
    cubicClosedNeighbors (object := object) (center := center) profile
  simpa [FinEnum.card_eq_fintypeCard] using
    Fintype.card_le_of_injective
      (fun member : {vertex : V // CubicClosedNeighbor (object := object)
        (center := center) profile vertex} => member.1) Subtype.val_injective

/-! ## CT14 exact unit-mass scan -/

def capability (profile : FanClosedPort.FanWindowProfile V) :
    CT14.Capability base.problem where
  Member := {vertex : V // CubicClosedNeighbor (object := object)
    (center := center) profile vertex}
  members := cubicClosedNeighbors (object := object) (center := center) profile
  Label := Unit
  labelDecidableEq := inferInstance
  memberLowerMass := fun _ctx _member => 1
  memberCapacity := fun _ctx _member => some 1
  memberLabel := fun _ctx _member => some ()

def context (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit))
    (object : FiniteObject V) (baseline : base.problem.Baseline object) :
    Core.BranchContext base.problem :=
  ⟨object, baseline, ()⟩

def input (profile : FanClosedPort.FanWindowProfile V) :
    CT14.Input (capability (base := base) (object := object) (center := center)
      profile) (context base object baseline) :=
  ⟨⟩

theorem lowerMass_eq_card (profile : FanClosedPort.FanWindowProfile V) :
    CT14.lowerMass
      (capability (base := base) (object := object) (center := center) profile)
      (context base object baseline) =
      (cubicClosedNeighbors (object := object) (center := center) profile).card := by
  change ((cubicClosedNeighbors (object := object) (center := center) profile
    ).orderedValues.map (fun _member => 1)).sum =
      (cubicClosedNeighbors (object := object) (center := center) profile).card
  simp

theorem upperCapacity_eq_card (profile : FanClosedPort.FanWindowProfile V) :
    CT14.upperCapacity
      (capability (base := base) (object := object) (center := center) profile)
      (context base object baseline) =
      (cubicClosedNeighbors (object := object) (center := center) profile).card := by
  change ((cubicClosedNeighbors (object := object) (center := center) profile
    ).orderedValues.map (fun _member => 1)).sum =
      (cubicClosedNeighbors (object := object) (center := center) profile).card
  simp

theorem multiplicity_eq_card (profile : FanClosedPort.FanWindowProfile V) :
    CT14.multiplicity
      (capability (base := base) (object := object) (center := center) profile)
      (context base object baseline) () =
      (cubicClosedNeighbors (object := object) (center := center) profile).card := by
  change (cubicClosedNeighbors (object := object) (center := center) profile
    ).orderedValues.foldl (fun count _member => count + 1) 0 =
      (cubicClosedNeighbors (object := object) (center := center) profile).card
  have foldOne : ∀ (values : List
      {vertex : V // CubicClosedNeighbor (object := object) (center := center)
        profile vertex}) (initial : Nat),
      values.foldl (fun count _member => count + 1) initial =
        initial + values.length := by
    intro values
    induction values with
    | nil => intro initial; simp
    | cons head tail ih =>
        intro initial
        rw [List.foldl_cons, ih]
        simp only [List.length_cons]
        omega
  rw [foldOne]
  simp

def sourceResidual (profile : FanClosedPort.FanWindowProfile V)
    (first second : FanClosedPort.OpenPort centerHigh deletionCritical)
    (assigned : FanClosedPort.AssignedPair centerHigh deletionCritical profile
      first second) :
    CT5.ChargeLedgerResidual
      (FanClosedPort.spec (base := base) centerHigh deletionCritical profile
        first second)
      (FanClosedPort.capability (base := base) centerHigh deletionCritical profile
        first second)
      (FanClosedPort.input base object baseline) := by
  let result := FanClosedPort.run (base := base) (baseline := baseline)
      centerHigh deletionCritical profile first second
  have terminal : result.terminal = .charge :=
    FanClosedPort.run_terminal_charge (base := base) (baseline := baseline)
      centerHigh deletionCritical profile first second assigned
  exact CT5.ExecutionResult.chargeResidual
    (FanClosedPort.spec (base := base) centerHigh deletionCritical profile
      first second)
    (FanClosedPort.capability (base := base) centerHigh deletionCritical profile
      first second)
    (FanClosedPort.input base object baseline) result terminal

def routedInput (profile : FanClosedPort.FanWindowProfile V)
    (first second : FanClosedPort.OpenPort centerHigh deletionCritical)
    (assigned : FanClosedPort.AssignedPair centerHigh deletionCritical profile
      first second) :=
  Routes.CT5ToCT14.buildInput
    (capability (base := base) (object := object) (center := center) profile)
    (sourceResidual (base := base) (baseline := baseline) centerHigh
      deletionCritical profile first second assigned)

def run (profile : FanClosedPort.FanWindowProfile V)
    (first second : FanClosedPort.OpenPort centerHigh deletionCritical)
    (assigned : FanClosedPort.AssignedPair centerHigh deletionCritical profile
      first second) :=
  CT14.run
    (capability (base := base) (object := object) (center := center) profile)
    (context base object baseline)
    (routedInput (base := base) (baseline := baseline) centerHigh
      deletionCritical profile first second assigned)

theorem run_terminal_capacity (profile : FanClosedPort.FanWindowProfile V)
    (first second : FanClosedPort.OpenPort centerHigh deletionCritical)
    (assigned : FanClosedPort.AssignedPair centerHigh deletionCritical profile
      first second) :
    (run (base := base) (baseline := baseline) centerHigh deletionCritical
      profile first second assigned).terminal = .capacity := by
  apply CT14.run_terminal_capacity_of_complete
  · intro member; exact ⟨1, rfl⟩
  · intro member; exact ⟨(), rfl⟩
  · rw [lowerMass_eq_card (base := base) (baseline := baseline)
      (center := center) profile,
      upperCapacity_eq_card (base := base) (baseline := baseline)
        (center := center) profile]

theorem run_trace_capacity (profile : FanClosedPort.FanWindowProfile V)
    (first second : FanClosedPort.OpenPort centerHigh deletionCritical)
    (assigned : FanClosedPort.AssignedPair centerHigh deletionCritical profile
      first second) :
    (run (base := base) (baseline := baseline) centerHigh deletionCritical
      profile first second assigned).trace =
      [.entry, .lowerMass, .memberScan, .upperCapacity, .comparison,
        .capacityTerminal] := by
  apply CT14.run_trace_capacity_of_complete
  · intro member; exact ⟨1, rfl⟩
  · intro member; exact ⟨(), rfl⟩
  · rw [lowerMass_eq_card (base := base) (baseline := baseline)
      (center := center) profile,
      upperCapacity_eq_card (base := base) (baseline := baseline)
        (center := center) profile]

/-- Four CT14 passes over a subtype predicate whose universal assignment test
scans at most `n` vertices, plus the final comparison. -/
def checks : Nat :=
  4 * object.input.vertices.card ^ 2 +
    4 * object.input.vertices.card + 1

def deficitNumerator (degree closedCount : Nat) : Int :=
  4 * (closedCount : Int) + (degree : Int) - 11

theorem deficitNumerator_ge_degree_sub_three
    {degree closedCount : Nat} (twoLe : 2 ≤ closedCount) :
    (degree : Int) - 3 ≤ deficitNumerator degree closedCount := by
  unfold deficitNumerator
  omega

theorem deficitNumerator_positive
    {degree closedCount : Nat} (degreeHigh : 4 ≤ degree)
    (twoLe : 2 ≤ closedCount) :
    0 < deficitNumerator degree closedCount := by
  have := deficitNumerator_ge_degree_sub_three (degree := degree) twoLe
  omega

structure VerifiedStage (profile : FanClosedPort.FanWindowProfile V)
    (first second : FanClosedPort.OpenPort centerHigh deletionCritical)
    (pair : FanClosedPort.CompatiblePair centerHigh deletionCritical first second)
    (assigned : FanClosedPort.AssignedPair centerHigh deletionCritical profile
      first second) : Prop where
  previous : FanClosedPort.VerifiedStage
    (base := base) (baseline := baseline) centerHigh deletionCritical profile
    first second pair assigned
  routeId : ((Routes.CT5ToCT14.rule
    (capability (base := base) (object := object) (center := center) profile)
    ).generate
      (sourceResidual (base := base) (baseline := baseline) centerHigh
        deletionCritical profile first second assigned) ()).routeId =
      "CT5.residual.chargeLedger->CT14"
  terminal : (run (base := base) (baseline := baseline) centerHigh
    deletionCritical profile first second assigned).terminal = .capacity
  trace : (run (base := base) (baseline := baseline) centerHigh
    deletionCritical profile first second assigned).trace =
    [.entry, .lowerMass, .memberScan, .upperCapacity, .comparison,
      .capacityTerminal]
  countAtLeastTwo : 2 ≤ (cubicClosedNeighbors (object := object)
    (center := center) profile).card
  multiplicityExact : CT14.multiplicity
    (capability (base := base) (object := object) (center := center) profile)
    (context base object baseline) () =
    (cubicClosedNeighbors (object := object) (center := center) profile).card
  positiveDeficit : 0 < deficitNumerator (object.degree center)
    (cubicClosedNeighbors (object := object) (center := center) profile).card
  total : ∃ result : CT14.ExecutionResult
      (capability (base := base) (object := object) (center := center) profile)
      (context base object baseline),
    result.outcome.Valid ∧ @CT14.Graph.ValidTrace base.problem
      (capability (base := base) (object := object) (center := center) profile)
      (context base object baseline) result.trace
  polynomial : checks (object := object) ≤
    4 * object.input.vertices.card ^ 2 +
      4 * object.input.vertices.card + 1

def verifiedStage (profile : FanClosedPort.FanWindowProfile V)
    (first second : FanClosedPort.OpenPort centerHigh deletionCritical)
    (pair : FanClosedPort.CompatiblePair centerHigh deletionCritical first second)
    (assigned : FanClosedPort.AssignedPair centerHigh deletionCritical profile
      first second) :
    VerifiedStage (base := base) (baseline := baseline) centerHigh
      deletionCritical profile first second pair assigned := by
  let source := sourceResidual (base := base) (baseline := baseline) centerHigh
    deletionCritical profile first second assigned
  have countAtLeastTwo := two_le_cubicClosed_card centerHigh deletionCritical
    profile first second pair assigned
  exact {
    previous := FanClosedPort.verifiedStage centerHigh deletionCritical profile
      first second pair assigned
    routeId := Routes.CT5ToCT14.generated_route_id
      (capability (base := base) (object := object) (center := center) profile)
      source
    terminal := run_terminal_capacity centerHigh deletionCritical profile first
      second assigned
    trace := run_trace_capacity centerHigh deletionCritical profile first second
      assigned
    countAtLeastTwo := countAtLeastTwo
    multiplicityExact := multiplicity_eq_card profile
    positiveDeficit := deficitNumerator_positive centerHigh countAtLeastTwo
    total := CT14.run_total
      (capability (base := base) (object := object) (center := center) profile)
      (context base object baseline)
      (routedInput (base := base) (baseline := baseline) centerHigh
        deletionCritical profile first second assigned)
    polynomial := by rfl
  }

end StructuralExhaustion.Graph.FanClosedPortMass
