import Mathlib.Tactic
import StructuralExhaustion.CT6.Automation
import StructuralExhaustion.CT9.Automation
import StructuralExhaustion.CT10.Automation
import StructuralExhaustion.Graph.MinimumDegreeCycle
import StructuralExhaustion.Graph.HighCenterPort
import StructuralExhaustion.Routes.CT6ToCT9
import StructuralExhaustion.Routes.Accumulated

namespace StructuralExhaustion.Graph.SurplusPortActivity

open StructuralExhaustion

universe u v

/-!
# Degree-surplus activity

This profile implements the finite, ordered part of the surplus-port
argument.  It scans the declared vertex order exactly once.  A high centre
fails precisely when it has a neighbour which is not cubic.  Thus the
first-failure terminal exposes the first bad centre, while the active-ledger
terminal proves the cubic-neighbour condition at every high centre and sums
the exact degree surplus.

No paths, subgraphs, graphs, or attachment codes are enumerated here.
-/

/-- One formal unit of degree above three at a centre.  The slot is deliberately
separate from the later choice of an incident edge: its cardinality is exactly
the manuscript surplus, without making a hidden choice of neighbours. -/
abbrev ExcessPortSlot {V : Type u} (object : FiniteObject V) :=
  (center : V) × Fin (object.degree center - 3)

@[implicit_reducible]
def portSlots {V : Type u} (object : FiniteObject V) :
    FinEnum (ExcessPortSlot object) := by
  letI : FinEnum V := object.input.vertices
  infer_instance

/-- The exact cardinality of the canonical surplus-slot universe. -/
theorem portSlots_card_eq_surplus {V : Type u}
    (object : FiniteObject V) :
    (portSlots object).card =
      (object.input.vertices.orderedValues.map
        (fun center => object.degree center - 3)).sum := by
  letI : FinEnum V := object.input.vertices
  rw [FinEnum.card_eq_fintypeCard, FinEnum.sum_orderedValues]
  simp [ExcessPortSlot, Fintype.card_sigma]

theorem degree_le_vertexCount {V : Type u} (object : FiniteObject V)
    (center : V) : object.degree center ≤ object.input.vertices.card := by
  have lengthEq :
      (object.input.orderedNeighbors center).values.length =
        object.degree center := by
    simpa [FiniteObject.degree] using
      object.input.orderedNeighbors_length center
  rw [← lengthEq]
  calc
    (object.input.orderedNeighbors center).values.length ≤
        object.input.vertices.orderedValues.length := by
      exact List.length_filter_le _ _
    _ = object.input.vertices.card := by
      simp [FinEnum.orderedValues, FinEnum.toList]

/-- The dependent surplus-slot family is at most quadratic in the declared
vertex count. -/
theorem portSlots_card_le_square {V : Type u} (object : FiniteObject V) :
    (portSlots object).card ≤ object.input.vertices.card ^ 2 := by
  letI : FinEnum V := object.input.vertices
  rw [portSlots_card_eq_surplus, FinEnum.sum_orderedValues]
  calc
    ∑ center, (object.degree center - 3) ≤
        ∑ _center : V, object.input.vertices.card :=
      Finset.sum_le_sum fun center _member =>
        (Nat.sub_le _ _).trans (degree_le_vertexCount object center)
    _ = object.input.vertices.card * object.input.vertices.card := by
      simp [FinEnum.card_eq_fintypeCard]
    _ = object.input.vertices.card ^ 2 := by ring

/-- A surplus-slot index is valid in its centre's neighbour schedule. -/
theorem portIndex_lt_neighbors {V : Type u} (object : FiniteObject V)
    (slot : ExcessPortSlot object) : slot.2.1 <
      (object.input.orderedNeighbors slot.1).values.length := by
  rw [object.input.orderedNeighbors_length]
  exact slot.2.isLt.trans_le (Nat.sub_le _ _)

/-- The all-incident-port index selected by a surplus slot. -/
def portOfSlot {V : Type u} (object : FiniteObject V)
    (slot : ExcessPortSlot object) : HighCenterPort.Port object slot.1 :=
  ⟨slot.2.1, portIndex_lt_neighbors object slot⟩

/-- The canonical incident port selected by a surplus slot. -/
def portEndpoint {V : Type u} (object : FiniteObject V)
    (slot : ExcessPortSlot object) : V :=
  HighCenterPort.endpoint object slot.1 (portOfSlot object slot)

theorem portEndpoint_adjacent {V : Type u} (object : FiniteObject V)
    (slot : ExcessPortSlot object) :
    object.graph.Adj slot.1 (portEndpoint object slot) :=
  HighCenterPort.endpoint_adjacent object slot.1 (portOfSlot object slot)

/-- At a fixed centre, distinct surplus slots select distinct incident
ports.  This is the reusable injectivity fact behind all later pair
interpretations; it depends only on the declared noduplicated neighbour
order. -/
theorem portEndpoint_injective_of_sameCenter {V : Type u}
    (object : FiniteObject V) {first second : ExcessPortSlot object}
    (sameCenter : first.1 = second.1)
    (sameEndpoint : portEndpoint object first = portEndpoint object second) :
    first = second := by
  rcases first with ⟨firstCenter, firstIndex⟩
  rcases second with ⟨secondCenter, secondIndex⟩
  dsimp only at sameCenter
  subst secondCenter
  have indexEq :
      (⟨firstIndex.1, portIndex_lt_neighbors object
        ⟨firstCenter, firstIndex⟩⟩ :
          Fin (object.input.orderedNeighbors firstCenter).values.length) =
      ⟨secondIndex.1, portIndex_lt_neighbors object
        ⟨firstCenter, secondIndex⟩⟩ :=
    (object.input.orderedNeighbors firstCenter).nodup.injective_get
      sameEndpoint
  have valueEq : firstIndex.1 = secondIndex.1 :=
    congrArg (fun index :
      Fin (object.input.orderedNeighbors firstCenter).values.length =>
        index.1) indexEq
  have finEq : firstIndex = secondIndex := Fin.ext valueEq
  subst secondIndex
  rfl

theorem portCenter_high {V : Type u} (object : FiniteObject V)
    (slot : ExcessPortSlot object) : 4 ≤ object.degree slot.1 := by
  have positive : 0 < object.degree slot.1 - 3 :=
    Nat.zero_lt_of_lt slot.2.isLt
  omega

theorem portEndpoint_cubic_of_deletionCritical {V : Type u}
    (object : FiniteObject V) (slot : ExcessPortSlot object)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3) :
    object.degree (portEndpoint object slot) = 3 := by
  have critical := deletionCritical
    ⟨(slot.1, portEndpoint object slot), portEndpoint_adjacent object slot⟩
  change object.degree slot.1 = 3 ∨
    object.degree (portEndpoint object slot) = 3 at critical
  rcases critical with centerCubic | endpointCubic
  · have high := portCenter_high object slot
    omega
  · exact endpointCubic

/-- The two non-centre neighbours of the cubic port endpoint, in declared
order. -/
def shoulderVertices {V : Type u} (object : FiniteObject V)
    (slot : ExcessPortSlot object) : List V :=
  HighCenterPort.shoulderVertices object slot.1 (portOfSlot object slot)

theorem shoulderVertices_length {V : Type u} (object : FiniteObject V)
    (slot : ExcessPortSlot object)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3) :
    (shoulderVertices object slot).length = 2 :=
  HighCenterPort.shoulderVertices_length object slot.1
    (portCenter_high object slot) deletionCritical (portOfSlot object slot)

def firstShoulder {V : Type u} (object : FiniteObject V)
    (slot : ExcessPortSlot object)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3) : V :=
  HighCenterPort.firstShoulder object slot.1 (portCenter_high object slot)
    deletionCritical (portOfSlot object slot)

def secondShoulder {V : Type u} (object : FiniteObject V)
    (slot : ExcessPortSlot object)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3) : V :=
  HighCenterPort.secondShoulder object slot.1 (portCenter_high object slot)
    deletionCritical (portOfSlot object slot)

/-- The two exact manuscript port types, specialized from the all-incident
high-centre profile. -/
abbrev PortType := HighCenterPort.PortType

@[implicit_reducible]
def portTypes : FinEnum PortType :=
  HighCenterPort.portTypes

def portType {V : Type u} (object : FiniteObject V)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3)
    (slot : ExcessPortSlot object) : PortType :=
  HighCenterPort.portType object slot.1 (portCenter_high object slot)
    deletionCritical (portOfSlot object slot)

def classificationCapability {V : Type u}
    (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit))
    (object : FiniteObject V)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3) :
    CT10.Capability base.problem where
  Datum := ExcessPortSlot object
  Class := PortType
  Promotion := PortType
  classes := portTypes
  classOf := portType object deletionCritical
  Direct := fun _portType => False
  directDecidable := fun _portType => isFalse id
  promote := id

def classificationInput {V : Type u}
    (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit))
    (object : FiniteObject V) (baseline : base.problem.Baseline object)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3) :
    CT10.Input (classificationCapability base object deletionCritical) where
  context := ⟨object, baseline, ()⟩
  data := (portSlots object).toOrderedCollection

/-- Source-polymorphic mathematical adapter for the ordinary accumulated
CT1→CT10 handoff.  It exposes the already declared surplus-slot schedule and
never inspects, rebuilds, or truncates the incoming proof ledger. -/
def classificationAdapter {V : Type u} {Source : Sort v}
    (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit))
    (object : FiniteObject V) (baseline : base.problem.Baseline object)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3) :
    Routes.Accumulated.Adapter Source
      (classificationCapability base object deletionCritical).executableInterface where
  targetContext := fun _source =>
    (classificationInput base object baseline deletionCritical).context
  trigger := fun _source =>
    ⟨(classificationInput base object baseline deletionCritical).data⟩

def classificationRun {V : Type u}
    (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit))
    (object : FiniteObject V) (baseline : base.problem.Baseline object)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3) :=
  CT10.run (classificationCapability base object deletionCritical)
    (classificationInput base object baseline deletionCritical)

theorem classificationRun_verified {V : Type u}
    (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit))
    (object : FiniteObject V) (baseline : base.problem.Baseline object)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3) :
    (classificationRun base object baseline deletionCritical).outcome.Valid :=
  CT10.run_verified _ _

theorem classificationRun_traceValid {V : Type u}
    (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit))
    (object : FiniteObject V) (baseline : base.problem.Baseline object)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3) :
    CT10.Graph.ValidTrace (classificationCapability base object deletionCritical)
      (classificationInput base object baseline deletionCritical)
      (classificationRun base object baseline deletionCritical).trace :=
  CT10.run_trace_valid _ _

theorem classificationRun_total {V : Type u}
    (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit))
    (object : FiniteObject V) (baseline : base.problem.Baseline object)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3) :
    ∃ result, result = classificationRun base object baseline deletionCritical ∧
      result.outcome.Valid :=
  ⟨_, rfl, classificationRun_verified base object baseline deletionCritical⟩

/-- Exact semantic split delivered by the CT10 terminal.  Either one of the
two port types is absent from the selected surplus slots, or both types have
an explicit slot. -/
theorem classificationResult_stateSpace {V : Type u}
    (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit))
    (object : FiniteObject V) (baseline : base.problem.Baseline object)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3)
    (result : CT10.ExecutionResult
      (classificationCapability base object deletionCritical)
      (classificationInput base object baseline deletionCritical)) :
    (∃ cls : PortType,
        CT10.row (classificationCapability base object deletionCritical)
          (classificationInput base object baseline deletionCritical) cls = []) ∨
      (∀ cls : PortType, ∃ slot : ExcessPortSlot object,
        slot ∈ CT10.row
          (classificationCapability base object deletionCritical)
          (classificationInput base object baseline deletionCritical) cls) := by
  cases result with
  | mk terminal path outcome =>
      cases outcome with
      | direct residual => exact residual.direct.elim
      | promoted residual => exact Or.inl ⟨residual.missing.cls,
          residual.missing.empty⟩
      | exhaustive certificate => exact Or.inr certificate.populated

theorem classification_stateSpace {V : Type u}
    (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit))
    (object : FiniteObject V) (baseline : base.problem.Baseline object)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3) :
    (∃ cls : PortType,
        CT10.row (classificationCapability base object deletionCritical)
          (classificationInput base object baseline deletionCritical) cls = []) ∨
      (∀ cls : PortType, ∃ slot : ExcessPortSlot object,
        slot ∈ CT10.row
          (classificationCapability base object deletionCritical)
          (classificationInput base object baseline deletionCritical) cls) :=
  classificationResult_stateSpace base object baseline deletionCritical
    (classificationRun base object baseline deletionCritical)

def classificationChecks {V : Type u} (object : FiniteObject V) : Nat :=
  2 * (portSlots object).card + 2

theorem classificationChecks_quadratic {V : Type u}
    (object : FiniteObject V) :
    classificationChecks object ≤ 2 * object.input.vertices.card ^ 2 + 2 := by
  unfold classificationChecks
  have slotsLe := portSlots_card_le_square object
  omega

/-- Reusable complete CT10 audit for the open/triangular surplus-port table. -/
structure VerifiedClassificationStage {V : Type u}
    (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit))
    (object : FiniteObject V) (baseline : base.problem.Baseline object)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3) : Prop where
  verified : (classificationRun base object baseline deletionCritical).outcome.Valid
  traceValid : CT10.Graph.ValidTrace
    (classificationCapability base object deletionCritical)
    (classificationInput base object baseline deletionCritical)
    (classificationRun base object baseline deletionCritical).trace
  total : ∃ result,
    result = classificationRun base object baseline deletionCritical ∧
      result.outcome.Valid
  stateSpace :
    (∃ cls : PortType,
        CT10.row (classificationCapability base object deletionCritical)
          (classificationInput base object baseline deletionCritical) cls = []) ∨
      (∀ cls : PortType, ∃ slot : ExcessPortSlot object,
        slot ∈ CT10.row
          (classificationCapability base object deletionCritical)
          (classificationInput base object baseline deletionCritical) cls)
  polynomial : classificationChecks object ≤
    2 * object.input.vertices.card ^ 2 + 2

def verifiedClassificationStage {V : Type u}
    (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit))
    (object : FiniteObject V) (baseline : base.problem.Baseline object)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3) :
    VerifiedClassificationStage base object baseline deletionCritical where
  verified := classificationRun_verified base object baseline deletionCritical
  traceValid := classificationRun_traceValid base object baseline deletionCritical
  total := classificationRun_total base object baseline deletionCritical
  stateSpace := classification_stateSpace base object baseline deletionCritical
  polynomial := classificationChecks_quadratic object

/-! ## CT9 refinement of open selected ports by centre -/

/-- Exact subtype of canonical surplus slots whose two shoulders are
nonadjacent. -/
abbrev OpenPortSlot {V : Type u} (object : FiniteObject V)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3) :=
  {slot : ExcessPortSlot object //
    portType object deletionCritical slot = .open}

@[implicit_reducible]
def openPortSlots {V : Type u} (object : FiniteObject V)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3) :
    FinEnum (OpenPortSlot object deletionCritical) :=
  Core.Enumeration.subtype (portSlots object)
    (fun slot => portType object deletionCritical slot = .open)
    (fun _slot => inferInstance)

theorem openPortSlots_card_le_portSlots {V : Type u}
    (object : FiniteObject V)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3) :
    (openPortSlots object deletionCritical).card ≤ (portSlots object).card := by
  letI : FinEnum (ExcessPortSlot object) := portSlots object
  letI : FinEnum (OpenPortSlot object deletionCritical) :=
    openPortSlots object deletionCritical
  simpa [FinEnum.card_eq_fintypeCard] using
    Fintype.card_le_of_injective
      (fun slot : OpenPortSlot object deletionCritical => slot.1)
      Subtype.val_injective

/-- Capacity-one centre fibres: overload means two open selected ports share
their centre. -/
def openPairCapability {V : Type u}
    (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit))
    (object : FiniteObject V)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3) :
    CT9.Capability base.problem where
  Item := OpenPortSlot object deletionCritical
  Label := V
  labels := object.input.vertices
  label := fun slot => slot.1.1
  capacity := fun _center => 1

def openPairInput {V : Type u}
    (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit))
    (object : FiniteObject V) (baseline : base.problem.Baseline object)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3) :
    CT9.Input (openPairCapability base object deletionCritical) where
  context := ⟨object, baseline, ()⟩
  items := (openPortSlots object deletionCritical).toOrderedCollection

/-- Source-polymorphic mathematical adapter for the ordinary accumulated
CT10→CT9 handoff.  The target receives exactly the canonical open-slot
subcollection; the complete incoming ledger remains framework-owned. -/
def openPairAdapter {V : Type u} {Source : Sort v}
    (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit))
    (object : FiniteObject V) (baseline : base.problem.Baseline object)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3) :
    Routes.Accumulated.Adapter Source
      (openPairCapability base object deletionCritical).executableInterface where
  targetContext := fun _source =>
    (openPairInput base object baseline deletionCritical).context
  trigger := fun _source =>
    ⟨(openPairInput base object baseline deletionCritical).items⟩

def openPairResult {V : Type u}
    (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit))
    (object : FiniteObject V) (baseline : base.problem.Baseline object)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3) :=
  CT9.run (openPairCapability base object deletionCritical)
    (openPairInput base object baseline deletionCritical)

/-- The semantic payload of an overloaded centre fibre. -/
structure SameCenterOpenPair {V : Type u}
    (object : FiniteObject V)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3) where
  first : ExcessPortSlot object
  second : ExcessPortSlot object
  firstOpen : portType object deletionCritical first = .open
  secondOpen : portType object deletionCritical second = .open
  distinct : first ≠ second
  sameCenter : first.1 = second.1

inductive OpenPairDecision {V : Type u}
    (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit))
    (object : FiniteObject V) (baseline : base.problem.Baseline object)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3) where
  | pair (value : SameCenterOpenPair object deletionCritical)
  | bounded (certificate : ∀ center,
      CT9.fibreCount (openPairCapability base object deletionCritical)
        (openPairInput base object baseline deletionCritical) center ≤ 1)

/-- Interpret an already executed CT9 terminal once, without a second search. -/
def openPairDecisionOfResult {V : Type u}
    (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit))
    (object : FiniteObject V) (baseline : base.problem.Baseline object)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3)
    (result : CT9.ExecutionResult
      (openPairCapability base object deletionCritical)
      (openPairInput base object baseline deletionCritical)) :
    OpenPairDecision base object baseline deletionCritical :=
  match result with
  | ⟨_, _, .overloaded residual⟩ =>
      let pair := residual.sameLabelPairOfCapacityOne rfl
      .pair {
        first := pair.first.1
        second := pair.second.1
        firstOpen := pair.first.2
        secondOpen := pair.second.2
        distinct := fun equal => pair.distinct (Subtype.ext equal)
        sameCenter := pair.labels_eq
      }
  | ⟨_, _, .bounded certificate⟩ => .bounded certificate.bounded

/-- Standalone interpretation of the graph profile's canonical execution. -/
def openPairDecision {V : Type u}
    (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit))
    (object : FiniteObject V) (baseline : base.problem.Baseline object)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3) :
    OpenPairDecision base object baseline deletionCritical :=
  openPairDecisionOfResult base object baseline deletionCritical
    (openPairResult base object baseline deletionCritical)

def openPairChecks {V : Type u} (object : FiniteObject V)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3) : Nat :=
  object.input.vertices.card * (openPortSlots object deletionCritical).card +
    object.input.vertices.card

/-- CT9 scans each supplied open slot once for each explicit centre label;
the declared family therefore has a cubic worst-case bound. -/
theorem openPairChecks_cubic {V : Type u} (object : FiniteObject V)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3) :
    openPairChecks object deletionCritical ≤
      object.input.vertices.card ^ 3 + object.input.vertices.card := by
  have openLe := openPortSlots_card_le_portSlots object deletionCritical
  have slotsLe := portSlots_card_le_square object
  unfold openPairChecks
  calc
    object.input.vertices.card * (openPortSlots object deletionCritical).card +
        object.input.vertices.card ≤
        object.input.vertices.card * object.input.vertices.card ^ 2 +
          object.input.vertices.card := by
      gcongr
      exact openLe.trans slotsLe
    _ = object.input.vertices.card ^ 3 +
          object.input.vertices.card := by ring

structure VerifiedOpenPairStage {V : Type u}
    (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit))
    (object : FiniteObject V) (baseline : base.problem.Baseline object)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3) : Prop where
  verified : (openPairResult base object baseline deletionCritical).outcome.Valid
  traceValid : CT9.Graph.ValidTrace
    (openPairCapability base object deletionCritical)
    (openPairInput base object baseline deletionCritical)
    (openPairResult base object baseline deletionCritical).trace
  exhaustive :
    (openPairResult base object baseline deletionCritical).terminal = .overloaded ∨
      (openPairResult base object baseline deletionCritical).terminal = .bounded
  polynomial : openPairChecks object deletionCritical ≤
    object.input.vertices.card ^ 3 + object.input.vertices.card

def verifiedOpenPairStage {V : Type u}
    (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit))
    (object : FiniteObject V) (baseline : base.problem.Baseline object)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3) :
    VerifiedOpenPairStage base object baseline deletionCritical where
  verified := CT9.run_verified _ _
  traceValid := CT9.run_trace_valid _ _
  exhaustive := CT9.outcome_exhaustive _ _ _
  polynomial := openPairChecks_cubic object deletionCritical

/-- The exact ordered CT6 specification on a finite graph object. -/
def spec {V : Type u} (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit)) :
    CT6.Spec base.problem where
  Index := V
  FailureData := Unit
  Failure := fun context center =>
    4 ≤ context.G.degree center ∧
      ∃ neighbor, context.G.graph.Adj center neighbor ∧
        context.G.degree neighbor ≠ 3
  failureData := fun _context _center _failure => ()
  contribution := fun context center => context.G.degree center - 3

/-- The scan order is the graph's declared vertex order.  Deciding one centre
uses only a bounded scan of that same vertex universe. -/
def capability {V : Type u}
    (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit))
    (object : FiniteObject V) : CT6.Capability (spec base) where
  failureOrder := object.input.vertices
  failureDecidable := by
    intro context center
    letI : FinEnum V := context.G.input.vertices
    letI : DecidableRel context.G.graph.Adj := context.G.input.decideAdj
    change Decidable
      (4 ≤ context.G.degree center ∧
        ∃ neighbor, context.G.graph.Adj center neighbor ∧
          context.G.degree neighbor ≠ 3)
    infer_instance

/-- The branch context used by the surplus audit. -/
def context {V : Type u}
    (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit))
    (object : FiniteObject V) (baseline : base.problem.Baseline object) :
    Core.BranchContext base.problem where
  G := object
  baseline := baseline
  state := ()

/-- Source-polymorphic mathematical adapter for an accumulated transition
into the ordered CT6 surplus audit.  The full predecessor is retained by the
framework; this profile supplies only the already selected graph context. -/
def activityAdapter {V : Type u} {Source : Sort v}
    (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit))
    (object : FiniteObject V) (baseline : base.problem.Baseline object) :
    Routes.Accumulated.Adapter Source
      (capability base object).executableInterface where
  targetContext := fun _source => context base object baseline
  trigger := fun _source => ()

/-- Deletion criticality rules out every monitored CT6 failure. -/
theorem noFailure_of_deletionCritical {V : Type u}
    (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit))
    (object : FiniteObject V) (baseline : base.problem.Baseline object)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3) :
    ∀ center, ¬(spec base).Failure (context base object baseline) center := by
  intro center failure
  rcases failure with ⟨centerHigh, neighbor, adjacent, neighborNotCubic⟩
  have critical := deletionCritical ⟨(center, neighbor), adjacent⟩
  change object.degree center = 3 ∨ object.degree neighbor = 3 at critical
  change 4 ≤ object.degree center at centerHigh
  change object.degree neighbor ≠ 3 at neighborNotCubic
  rcases critical with centerCubic | neighborCubic
  · omega
  · exact neighborNotCubic neighborCubic

/-- Exact active-ledger execution forced by deletion criticality. -/
def run {V : Type u}
    (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit))
    (object : FiniteObject V) (baseline : base.problem.Baseline object)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3) :
    CT6.ActiveLedgerRun (spec base) (capability base object)
      (context base object baseline) :=
  CT6.runActiveLedgerOfNoFailure (spec base) (capability base object)
    (context base object baseline)
    (noFailure_of_deletionCritical base object baseline deletionCritical)

/-- The ledger total is definitionally the ordered sum of `degree - 3`. -/
theorem run_total_eq_surplus {V : Type u}
    (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit))
    (object : FiniteObject V) (baseline : base.problem.Baseline object)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3) :
    (run base object baseline deletionCritical).residual.total =
      (object.input.vertices.orderedValues.map
        (fun center => object.degree center - 3)).sum := by
  rw [(run base object baseline deletionCritical).residual.computed]
  have foldSum : ∀ (values : List V) (initial : Nat),
      values.foldl (fun total center =>
        total + (object.degree center - 3)) initial =
      initial + (values.map (fun center => object.degree center - 3)).sum := by
    intro values
    induction values with
    | nil => intro initial; simp
    | cons head tail inductionHypothesis =>
        intro initial
        simp only [List.foldl_cons, List.map_cons, List.sum_cons]
        rw [inductionHypothesis]
        omega
  simpa [CT6.activeTotal, spec, capability, context] using
    foldSum object.input.vertices.orderedValues 0

/-- Exact handshake identity for an ordered degree-excess ledger above any
pointwise baseline.  The machine order affects execution only; its total is
the standard graph-theoretic quantity `2m - bound*n`. -/
theorem degreeExcess_sum_add_baseline {V : Type u}
    (object : FiniteObject V) (bound : Nat)
    (baseline : ∀ vertex, bound ≤ object.degree vertex) :
    (object.input.vertices.orderedValues.map
        (fun vertex => object.degree vertex - bound)).sum +
        bound * object.input.vertices.card =
      2 * object.edgeCount := by
  have listIdentity : ∀ values : List V,
      (values.map (fun vertex => object.degree vertex - bound)).sum +
          bound * values.length =
        (values.map object.degree).sum := by
    intro values
    induction values with
    | nil => simp
    | cons head tail ih =>
        simp only [List.map_cons, List.sum_cons, List.length_cons]
        have headBound := baseline head
        rw [Nat.mul_succ]
        omega
  have orderedIdentity :=
    listIdentity object.input.vertices.orderedValues
  rw [object.input.vertices.orderedValues_length] at orderedIdentity
  rw [orderedIdentity]
  letI : FinEnum V := object.input.vertices
  letI : DecidableRel object.graph.Adj := object.input.decideAdj
  rw [FinEnum.sum_orderedValues]
  change (∑ vertex, object.graph.degree vertex) =
    2 * object.graph.edgeFinset.card
  exact object.graph.sum_degrees_eq_twice_card_edges

/-- Integer form of the same exact ledger identity. -/
theorem degreeExcess_sum_int_eq {V : Type u}
    (object : FiniteObject V) (bound : Nat)
    (baseline : ∀ vertex, bound ≤ object.degree vertex) :
    ((object.input.vertices.orderedValues.map
        (fun vertex => object.degree vertex - bound)).sum : Int) =
      2 * (object.edgeCount : Int) -
        bound * (object.input.vertices.card : Int) := by
  have exactNat := degreeExcess_sum_add_baseline object bound baseline
  omega

/-- The selected slot universe has exactly the ledger cardinality.  This is
the formal excess-selector equation `|P_exc| = Σ_v (d(v)-3)`. -/
theorem excessPortSlot_card_eq_surplus {V : Type u}
    (object : FiniteObject V) :
    letI : FinEnum V := object.input.vertices
    Fintype.card (ExcessPortSlot object) =
      (object.input.vertices.orderedValues.map
        (fun center => object.degree center - 3)).sum := by
  letI : FinEnum V := object.input.vertices
  simpa [portSlots, FinEnum.card_eq_fintypeCard] using
    portSlots_card_eq_surplus object

/-- The CT6 active branch certifies the cubic endpoint of every incident port
at a high centre. -/
theorem run_highCenter_neighbor_cubic {V : Type u}
    (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit))
    (object : FiniteObject V) (baseline : base.problem.Baseline object)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3)
    {center neighbor : V} (centerHigh : 4 ≤ object.degree center)
    (adjacent : object.graph.Adj center neighbor) :
    object.degree neighbor = 3 := by
  have noFailure :=
    (run base object baseline deletionCritical).residual.noFailure center
  by_contra neighborNotCubic
  exact noFailure ⟨centerHigh, neighbor, adjacent, neighborNotCubic⟩

/-- CT6 performs one ordered failure test per vertex. -/
def checkCount {V : Type u} (object : FiniteObject V) : Nat :=
  object.input.vertices.orderedValues.length

theorem checkCount_eq_vertexCount {V : Type u} (object : FiniteObject V) :
    checkCount object = object.input.vertices.card := by
  simp [checkCount, FinEnum.orderedValues, FinEnum.toList]

/-- Linear native work certificate for the complete CT6 scan. -/
theorem checkCount_linear {V : Type u} (object : FiniteObject V) :
    checkCount object ≤ object.input.vertices.card + 1 := by
  rw [checkCount_eq_vertexCount]
  omega

/-- Conservative primitive bound: each of the `n` centre tests may inspect
the `n`-vertex neighbour schedule.  The runner never materializes their
Cartesian product. -/
def primitiveCheckBound {V : Type u} (object : FiniteObject V) : Nat :=
  object.input.vertices.card ^ 2

theorem primitiveCheckBound_quadratic {V : Type u}
    (object : FiniteObject V) :
    primitiveCheckBound object ≤ (object.input.vertices.card + 1) ^ 2 := by
  unfold primitiveCheckBound
  exact Nat.pow_le_pow_left (Nat.le_add_right _ _) 2

/-! ## Framework-owned CT6 to CT9 surplus-pair transition -/

/-- Exact dependent enumeration of the degree-surplus slots. -/
@[implicit_reducible]
def excessPortSlots {V : Type u} (object : FiniteObject V) :
    FinEnum (ExcessPortSlot object) :=
  portSlots object

/-- CT9's one-box, capacity-one profile.  An overload is exactly the
existence of two distinct surplus slots. -/
def pairCapability {V : Type u}
    (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit))
    (object : FiniteObject V) : CT9.Capability base.problem where
  Item := ExcessPortSlot object
  Label := Unit
  labels := Core.Enumeration.unit
  label := fun _slot => ()
  capacity := fun _label => 1

/-- The only semantic adapter needed by the registered transition: expose the
exact duplicate-free surplus-slot collection. -/
def pairAdapter {V : Type u}
    (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit))
    (object : FiniteObject V) (baseline : base.problem.Baseline object)
    (_deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3) :
    Routes.CT6ToCT9.ItemCollectionAdapter
      (CT6.ActiveLedgerResidual (spec base) (capability base object)
        (context base object baseline))
      (pairCapability base object).Item :=
  Routes.CT6ToCT9.ItemCollectionAdapter.constant
    (excessPortSlots object).toOrderedCollection

/-- Exact CT6 active-ledger stage supplied to the executable transition. -/
def pairSourceStage {V : Type u}
    (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit))
    (object : FiniteObject V) (baseline : base.problem.Baseline object)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3) :=
  Core.Routing.ResidualStage.exact (tactic := .ct6)
    (run base object baseline deletionCritical)

/-- Framework-owned CT6→CT9 transition for surplus slots. -/
abbrev pairTransition {V : Type u}
    (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit))
    (object : FiniteObject V) (baseline : base.problem.Baseline object)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3) :=
  Routes.CT6ToCT9.transition (pairCapability base object)
    (pairAdapter base object baseline deletionCritical)

/-- Enabled CT9 execution retaining the complete CT6 stage. -/
def pairStage {V : Type u}
    (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit))
    (object : FiniteObject V) (baseline : base.problem.Baseline object)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3) :=
  Routes.CT6ToCT9.advance (pairCapability base object)
    (pairAdapter base object baseline deletionCritical)
    (fun ledger => ledger.residual)
    (pairSourceStage base object baseline deletionCritical)

/-- Accumulated CT9 ledger passed to downstream framework transitions. -/
def pairLedger {V : Type u}
    (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit))
    (object : FiniteObject V) (baseline : base.problem.Baseline object)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3) :=
  pairStage base object baseline deletionCritical

/-- CT9 input read from the executable transition. -/
def pairInput {V : Type u}
    (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit))
    (object : FiniteObject V) (baseline : base.problem.Baseline object)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3) :
    CT9.Input (pairCapability base object) :=
  let transition := pairTransition base object baseline deletionCritical
  let execution := transition.onLedger (fun ledger => ledger.residual)
  let source := pairSourceStage base object baseline deletionCritical
  CT9.Input.ofTrigger (execution.targetContext source)
    (execution.trigger source ())

/-- The exact CT9 execution following the typed CT6 transition. -/
def pairResult {V : Type u}
    (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit))
    (object : FiniteObject V) (baseline : base.problem.Baseline object)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3) :=
  (pairStage base object baseline deletionCritical).output.targetResult

/-- Semantic state-space split extracted from the exact CT9 outcome. -/
inductive PairDecision {V : Type u}
    (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit))
    (object : FiniteObject V) (baseline : base.problem.Baseline object)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3) : Type u where
  | bounded
      (small : (pairInput base object baseline deletionCritical).items.values.length ≤ 1)
  | pair
      (value : CT9.SameLabelPair (pairCapability base object)
        (pairInput base object baseline deletionCritical) ())

/-- Interpret an already executed terminal-indexed CT9 outcome without
recomputing or reconstructing it. -/
def pairDecisionOfResult {V : Type u}
    (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit))
    (object : FiniteObject V) (baseline : base.problem.Baseline object)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3)
    (result : CT9.ExecutionResult (pairCapability base object)
      (pairInput base object baseline deletionCritical)) :
    PairDecision base object baseline deletionCritical :=
  match result with
  | ⟨_, _, .overloaded residual⟩ =>
      .pair (residual.sameLabelPairOfCapacityOne rfl)
  | ⟨_, _, .bounded certificate⟩ =>
      .bounded (by
        have global := certificate.cardinality_le_totalCapacity
        change (pairInput base object baseline deletionCritical).items.values.length ≤
          1 at global
        exact global)

/-- Standalone interpretation of the graph profile's canonical transition. -/
def pairDecision {V : Type u}
    (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit))
    (object : FiniteObject V) (baseline : base.problem.Baseline object)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3) :
    PairDecision base object baseline deletionCritical :=
  pairDecisionOfResult base object baseline deletionCritical
    (pairResult base object baseline deletionCritical)

theorem pairTransition_profile_id {V : Type u}
    (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit))
    (object : FiniteObject V) (baseline : base.problem.Baseline object)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3) :
    (pairTransition base object baseline deletionCritical).profileId =
      "CT6.residual.activeLedger->CT9" :=
  Routes.CT6ToCT9.transition_profile_id (pairCapability base object)
    (pairAdapter base object baseline deletionCritical)

theorem pairInput_context_preserved {V : Type u}
    (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit))
    (object : FiniteObject V) (baseline : base.problem.Baseline object)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3) :
    (pairInput base object baseline deletionCritical).context =
      context base object baseline :=
  rfl

theorem pairItemCount_eq_surplus {V : Type u}
    (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit))
    (object : FiniteObject V) (baseline : base.problem.Baseline object)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3) :
    (pairInput base object baseline deletionCritical).items.values.length =
      (object.input.vertices.orderedValues.map
        (fun center => object.degree center - 3)).sum := by
  change (excessPortSlots object).orderedValues.length = _
  rw [show (excessPortSlots object).orderedValues.length =
      (excessPortSlots object).card by
    simp [FinEnum.orderedValues, FinEnum.toList]]
  letI : FinEnum V := object.input.vertices
  rw [FinEnum.card_eq_fintypeCard]
  change Fintype.card (ExcessPortSlot object) = _
  rw [Fintype.card_sigma]
  simpa using (FinEnum.sum_orderedValues object.input.vertices
    (fun center => object.degree center - 3)).symm

/-- At least two surplus slots force the exact CT9 overload branch. -/
def pairRunOfTwoLe {V : Type u}
    (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit))
    (object : FiniteObject V) (baseline : base.problem.Baseline object)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3)
    (twoLe : 2 ≤
      (pairInput base object baseline deletionCritical).items.values.length) :
    CT9.OverloadedRun (pairCapability base object)
      (pairInput base object baseline deletionCritical) := by
  apply CT9.runOverloadedOfTotalCapacityLtCardinality
  change 1 < (pairInput base object baseline deletionCritical).items.values.length
  omega

/-- The two distinct surplus slots selected by the exact overloaded run. -/
def pairOfTwoLe {V : Type u}
    (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit))
    (object : FiniteObject V) (baseline : base.problem.Baseline object)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3)
    (twoLe : 2 ≤
      (pairInput base object baseline deletionCritical).items.values.length) :=
  CT9.OverloadedRun.sameLabelPairOfCapacityOne
    (pairCapability base object)
    (pairInput base object baseline deletionCritical)
    (pairRunOfTwoLe base object baseline deletionCritical twoLe) rfl

/-- If the exact slot family has at most one member, CT9 takes its bounded
branch with the dual typed trace. -/
def pairBoundedRunOfCardinalityLeOne {V : Type u}
    (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit))
    (object : FiniteObject V) (baseline : base.problem.Baseline object)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3)
    (small :
      (pairInput base object baseline deletionCritical).items.values.length ≤ 1) :
    CT9.BoundedRun (pairCapability base object)
      (pairInput base object baseline deletionCritical) := by
  apply CT9.runBoundedOfBounded
  intro label
  cases label
  simpa [CT9.fibreCount, CT9.fibre, pairCapability] using small

/-- Native linear scan bound for CT9's single label fibre. -/
theorem pairChecks_linear {V : Type u}
    (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit))
    (object : FiniteObject V) (baseline : base.problem.Baseline object)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3) :
    (pairInput base object baseline deletionCritical).items.values.length ≤
      (pairInput base object baseline deletionCritical).items.values.length + 1 := by
  omega

end StructuralExhaustion.Graph.SurplusPortActivity
