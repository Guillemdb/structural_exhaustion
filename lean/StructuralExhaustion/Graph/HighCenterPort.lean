import Mathlib.Tactic
import StructuralExhaustion.CT10.Automation
import StructuralExhaustion.Graph.HighCenterStructure

namespace StructuralExhaustion.Graph.HighCenterPort

open StructuralExhaustion

universe u

/-!
# All incident ports at a high centre

This profile is deliberately independent of any problem-specific excess-port
selector.  A port is an index in one centre's declared neighbour schedule, so
the finite CT10 datum collection has exactly `degree center` elements.  The
profile classifies those ports as open or triangular and derives the standard
four-cycle-free local dichotomy without enumerating pairs.
-/

/-- One actual incident port at `center`, represented by its position in the
declared neighbour schedule. -/
abbrev Port {V : Type u} (object : FiniteObject V) (center : V) :=
  Fin (object.input.orderedNeighbors center).values.length

@[implicit_reducible]
def ports {V : Type u} (object : FiniteObject V) (center : V) :
    FinEnum (Port object center) := by
  infer_instance

def endpoint {V : Type u} (object : FiniteObject V) (center : V)
    (port : Port object center) : V :=
  (object.input.orderedNeighbors center).values.get port

theorem endpoint_adjacent {V : Type u} (object : FiniteObject V) (center : V)
    (port : Port object center) :
    object.graph.Adj center (endpoint object center port) := by
  apply (object.input.mem_orderedNeighbors_iff _ _).1
  exact List.get_mem _ _

theorem endpoint_injective {V : Type u} (object : FiniteObject V)
    (center : V) {first second : Port object center}
    (same : endpoint object center first = endpoint object center second) :
    first = second :=
  (object.input.orderedNeighbors center).nodup.injective_get same

/-- Literal equivalence between port positions and actual neighbours.  This
is proof-level and reuses the declared neighbour order; it performs no search
beyond choosing the index already certified by list membership. -/
noncomputable def neighborEquiv {V : Type u} (object : FiniteObject V)
    (center : V) :
    Port object center ≃ {vertex : V // object.graph.Adj center vertex} where
  toFun := fun port => ⟨endpoint object center port,
    endpoint_adjacent object center port⟩
  invFun := fun neighbor =>
    Classical.choose (List.get_of_mem
      ((object.input.mem_orderedNeighbors_iff center neighbor.1).2
        neighbor.2))
  left_inv := by
    intro port
    apply endpoint_injective object center
    exact Classical.choose_spec (List.get_of_mem
      ((object.input.mem_orderedNeighbors_iff center
        (endpoint object center port)).2
          (endpoint_adjacent object center port)))
  right_inv := by
    intro neighbor
    apply Subtype.ext
    exact Classical.choose_spec (List.get_of_mem
      ((object.input.mem_orderedNeighbors_iff center neighbor.1).2
        neighbor.2))

theorem ports_card_eq_degree {V : Type u} (object : FiniteObject V)
    (center : V) : (ports object center).card = object.degree center := by
  rw [FinEnum.card_eq_fintypeCard, Fintype.card_fin]
  exact object.input.orderedNeighbors_length center

theorem endpoint_cubic {V : Type u} (object : FiniteObject V)
    (center : V) (centerHigh : 4 ≤ object.degree center)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3)
    (port : Port object center) :
    object.degree (endpoint object center port) = 3 := by
  have critical := deletionCritical
    ⟨(center, endpoint object center port), endpoint_adjacent object center port⟩
  change object.degree center = 3 ∨
    object.degree (endpoint object center port) = 3 at critical
  omega

/-- The two non-centre neighbours of a cubic port endpoint. -/
def shoulderVertices {V : Type u} (object : FiniteObject V) (center : V)
    (port : Port object center) : List V := by
  letI : DecidableEq V := object.input.vertices.decEq
  exact (object.input.orderedNeighbors (endpoint object center port)).values.erase center

theorem shoulderVertices_length {V : Type u} (object : FiniteObject V)
    (center : V) (centerHigh : 4 ≤ object.degree center)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3)
    (port : Port object center) :
    (shoulderVertices object center port).length = 2 := by
  letI : DecidableEq V := object.input.vertices.decEq
  rw [shoulderVertices, List.length_erase_of_mem]
  · rw [object.input.orderedNeighbors_length]
    change object.degree (endpoint object center port) - 1 = 2
    rw [endpoint_cubic object center centerHigh deletionCritical port]
  · exact (object.input.mem_orderedNeighbors_iff _ _).2
      (endpoint_adjacent object center port).symm

def firstShoulder {V : Type u} (object : FiniteObject V) (center : V)
    (centerHigh : 4 ≤ object.degree center)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3)
    (port : Port object center) : V :=
  (shoulderVertices object center port)[0]'(by
    rw [shoulderVertices_length object center centerHigh deletionCritical port]
    decide)

def secondShoulder {V : Type u} (object : FiniteObject V) (center : V)
    (centerHigh : 4 ≤ object.degree center)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3)
    (port : Port object center) : V :=
  (shoulderVertices object center port)[1]'(by
    rw [shoulderVertices_length object center centerHigh deletionCritical port]
    decide)

inductive PortType where
  | open
  | triangular
  deriving Repr, DecidableEq

@[implicit_reducible]
def portTypes : FinEnum PortType :=
  FinEnum.ofNodupList [.open, .triangular]
    (by intro portType; cases portType <;> simp) (by decide)

def portType {V : Type u} (object : FiniteObject V) (center : V)
    (centerHigh : 4 ≤ object.degree center)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3)
    (port : Port object center) : PortType := by
  letI : DecidableRel object.graph.Adj := object.input.decideAdj
  exact if object.graph.Adj
      (firstShoulder object center centerHigh deletionCritical port)
      (secondShoulder object center centerHigh deletionCritical port)
    then .triangular else .open

abbrev OpenPort {V : Type u} (object : FiniteObject V) (center : V)
    (centerHigh : 4 ≤ object.degree center)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3) :=
  {port : Port object center //
    portType object center centerHigh deletionCritical port = .open}

abbrev TriangularPort {V : Type u} (object : FiniteObject V) (center : V)
    (centerHigh : 4 ≤ object.degree center)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3) :=
  {port : Port object center //
    portType object center centerHigh deletionCritical port = .triangular}

@[implicit_reducible]
def triangularPorts {V : Type u} (object : FiniteObject V) (center : V)
    (centerHigh : 4 ≤ object.degree center)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3) :
    FinEnum (TriangularPort object center centerHigh deletionCritical) :=
  Core.Enumeration.subtype (ports object center)
    (fun port => portType object center centerHigh deletionCritical port =
      .triangular)
    (fun _port => inferInstance)

theorem triangularPorts_card_le_ports {V : Type u}
    (object : FiniteObject V) (center : V)
    (centerHigh : 4 ≤ object.degree center)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3) :
    (triangularPorts object center centerHigh deletionCritical).card ≤
      (ports object center).card := by
  letI : FinEnum (Port object center) := ports object center
  letI : FinEnum (TriangularPort object center centerHigh deletionCritical) :=
    triangularPorts object center centerHigh deletionCritical
  simpa [FinEnum.card_eq_fintypeCard] using
    Fintype.card_le_of_injective
      (fun port : TriangularPort object center centerHigh deletionCritical =>
        port.1) Subtype.val_injective

/-- Exact manuscript compatibility predicate for any two ports at one centre. -/
def FanCompatible {V : Type u} (object : FiniteObject V) (center : V)
    (first second : Port object center) : Prop :=
  endpoint object center first ∉ shoulderVertices object center second ∧
    endpoint object center second ∉ shoulderVertices object center first ∧
    List.Disjoint (shoulderVertices object center first)
      (shoulderVertices object center second)

theorem adjacent_of_mem_shoulders {V : Type u} (object : FiniteObject V)
    (center : V) (port : Port object center) {vertex : V}
    (member : vertex ∈ shoulderVertices object center port) :
    object.graph.Adj (endpoint object center port) vertex := by
  letI : DecidableEq V := object.input.vertices.decEq
  apply (object.input.mem_orderedNeighbors_iff _ _).1
  exact List.mem_of_mem_erase member

theorem ne_center_of_mem_shoulders {V : Type u} (object : FiniteObject V)
    (center : V) (port : Port object center) {vertex : V}
    (member : vertex ∈ shoulderVertices object center port) :
    vertex ≠ center := by
  letI : DecidableEq V := object.input.vertices.decEq
  intro equal
  subst vertex
  have nodup :=
    (object.input.orderedNeighbors (endpoint object center port)).nodup
  rw [shoulderVertices, nodup.erase_eq_filter] at member
  simp at member

theorem firstShoulder_mem {V : Type u} (object : FiniteObject V)
    (center : V) (centerHigh : 4 ≤ object.degree center)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3)
    (port : Port object center) :
    firstShoulder object center centerHigh deletionCritical port ∈
      shoulderVertices object center port := by
  unfold firstShoulder
  exact List.get_mem _ _

theorem secondShoulder_mem {V : Type u} (object : FiniteObject V)
    (center : V) (centerHigh : 4 ≤ object.degree center)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3)
    (port : Port object center) :
    secondShoulder object center centerHigh deletionCritical port ∈
      shoulderVertices object center port := by
  unfold secondShoulder
  exact List.get_mem _ _

/-- Every non-centre neighbour of a cubic port endpoint is one of the two
declared shoulders. -/
theorem mem_shoulders_of_adjacent_endpoint_of_ne_center {V : Type u}
    (object : FiniteObject V) (center : V) (port : Port object center)
    {vertex : V}
    (adjacent : object.graph.Adj (endpoint object center port) vertex)
    (neCenter : vertex ≠ center) :
    vertex ∈ shoulderVertices object center port := by
  letI : DecidableEq V := object.input.vertices.decEq
  unfold shoulderVertices
  exact (List.mem_erase_of_ne neCenter).2
    ((object.input.mem_orderedNeighbors_iff _ _).2 adjacent)

/-- The length-two shoulder list has no hidden third case. -/
theorem eq_firstShoulder_or_eq_secondShoulder_of_mem {V : Type u}
    (object : FiniteObject V) (center : V)
    (centerHigh : 4 ≤ object.degree center)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3)
    (port : Port object center) {vertex : V}
    (member : vertex ∈ shoulderVertices object center port) :
    vertex = firstShoulder object center centerHigh deletionCritical port ∨
      vertex = secondShoulder object center centerHigh deletionCritical port := by
  obtain ⟨index, indexEq⟩ := List.get_of_mem member
  have indexLt : index.val < 2 := by
    simpa only [shoulderVertices_length object center centerHigh
      deletionCritical port] using index.isLt
  by_cases indexZero : index.val = 0
  · left
    rw [← indexEq]
    unfold firstShoulder
    apply congrArg (List.get (shoulderVertices object center port))
    exact Fin.ext indexZero
  · have indexOne : index.val = 1 := by omega
    right
    rw [← indexEq]
    unfold secondShoulder
    apply congrArg (List.get (shoulderVertices object center port))
    exact Fin.ext indexOne

theorem firstShoulder_ne_secondShoulder {V : Type u}
    (object : FiniteObject V) (center : V)
    (centerHigh : 4 ≤ object.degree center)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3)
    (port : Port object center) :
    firstShoulder object center centerHigh deletionCritical port ≠
      secondShoulder object center centerHigh deletionCritical port := by
  letI : DecidableEq V := object.input.vertices.decEq
  intro equal
  have nodup : (shoulderVertices object center port).Nodup := by
    unfold shoulderVertices
    exact (object.input.orderedNeighbors (endpoint object center port)).nodup.erase _
  have indexEq := nodup.injective_get equal
  have valueEq := congrArg Fin.val indexEq
  norm_num at valueEq

/-- Exact induced-core degree of a cubic fan neighbour.  Once the center is
in the core, its only possible additional core neighbours are the two literal
shoulders. -/
theorem inducedCoreDegree_eq_one_add_shoulders {V : Type u}
    (object : FiniteObject V) (center : V)
    (centerHigh : 4 ≤ object.degree center)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3)
    (core : Finset V) (centerMem : center ∈ core)
    (port : Port object center) :
    (letI : FinEnum V := object.input.vertices
     letI : DecidableEq V := object.input.vertices.decEq
     letI : DecidableRel object.graph.Adj := object.input.decideAdj
     (object.graph.neighborFinset (endpoint object center port) ∩ core).card =
        1 + (if firstShoulder object center centerHigh deletionCritical port ∈ core
          then 1 else 0) +
          (if secondShoulder object center centerHigh deletionCritical port ∈ core
            then 1 else 0)) := by
  letI : FinEnum V := object.input.vertices
  letI : DecidableEq V := object.input.vertices.decEq
  letI : DecidableRel object.graph.Adj := object.input.decideAdj
  let endpointVertex := endpoint object center port
  let first := firstShoulder object center centerHigh deletionCritical port
  let second := secondShoulder object center centerHigh deletionCritical port
  let coreNeighbors := object.graph.neighborFinset endpointVertex ∩ core
  let retainedShoulders := ({first, second} : Finset V).filter fun vertex =>
    vertex ∈ core
  have neighborSetEq : coreNeighbors = insert center retainedShoulders := by
    ext other
    constructor
    · intro member
      have adjacent : object.graph.Adj endpointVertex other := by
        simpa [SimpleGraph.mem_neighborFinset] using
          (Finset.mem_inter.mp member).1
      have otherCore := (Finset.mem_inter.mp member).2
      by_cases equalCenter : other = center
      · subst other
        simp
      · have shoulderMember :=
          mem_shoulders_of_adjacent_endpoint_of_ne_center object center port
            adjacent equalCenter
        rcases eq_firstShoulder_or_eq_secondShoulder_of_mem object center
            centerHigh deletionCritical port shoulderMember with
          equalFirst | equalSecond
        · subst other
          simp [retainedShoulders, first, second, otherCore]
        · subst other
          simp [retainedShoulders, first, second, otherCore]
    · intro member
      simp only [Finset.mem_insert] at member
      rcases member with equalCenter | shoulderMember
      · subst other
        apply Finset.mem_inter.mpr
        exact ⟨by simpa [SimpleGraph.mem_neighborFinset, endpointVertex] using
          (endpoint_adjacent object center port).symm, centerMem⟩
      · have shoulderCore : other ∈ core :=
          (Finset.mem_filter.mp shoulderMember).2
        have shoulderCases : other = first ∨ other = second := by
          simpa [retainedShoulders] using
            (Finset.mem_filter.mp shoulderMember).1
        apply Finset.mem_inter.mpr
        constructor
        · rw [SimpleGraph.mem_neighborFinset]
          rcases shoulderCases with rfl | rfl
          · exact adjacent_of_mem_shoulders object center port
              (firstShoulder_mem object center centerHigh deletionCritical port)
          · exact adjacent_of_mem_shoulders object center port
              (secondShoulder_mem object center centerHigh deletionCritical port)
        · exact shoulderCore
  change coreNeighbors.card =
    1 + (if first ∈ core then 1 else 0) +
      (if second ∈ core then 1 else 0)
  rw [neighborSetEq]
  have centerNotRetained : center ∉ retainedShoulders := by
    intro member
    have shoulderCases : center = first ∨ center = second := by
      simpa [retainedShoulders] using (Finset.mem_filter.mp member).1
    rcases shoulderCases with equalFirst | equalSecond
    · exact (ne_center_of_mem_shoulders object center port
        (firstShoulder_mem object center centerHigh deletionCritical port))
        equalFirst.symm
    · exact (ne_center_of_mem_shoulders object center port
        (secondShoulder_mem object center centerHigh deletionCritical port))
        equalSecond.symm
  rw [Finset.card_insert_of_notMem centerNotRetained]
  have firstNeSecond : first ≠ second :=
    firstShoulder_ne_secondShoulder object center centerHigh
      deletionCritical port
  by_cases firstCore : first ∈ core <;>
    by_cases secondCore : second ∈ core <;>
      unfold retainedShoulders <;>
      rw [Finset.filter_insert, Finset.filter_singleton] <;>
      simp [firstCore, secondCore, firstNeSecond]

theorem firstShoulder_adjacent_endpoint {V : Type u}
    (object : FiniteObject V) (center : V)
    (centerHigh : 4 ≤ object.degree center)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3)
    (port : Port object center) :
    object.graph.Adj
      (firstShoulder object center centerHigh deletionCritical port)
      (endpoint object center port) :=
  (adjacent_of_mem_shoulders object center port
    (firstShoulder_mem object center centerHigh deletionCritical port)).symm

theorem secondShoulder_adjacent_endpoint {V : Type u}
    (object : FiniteObject V) (center : V)
    (centerHigh : 4 ≤ object.degree center)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3)
    (port : Port object center) :
    object.graph.Adj
      (secondShoulder object center centerHigh deletionCritical port)
      (endpoint object center port) :=
  (adjacent_of_mem_shoulders object center port
    (secondShoulder_mem object center centerHigh deletionCritical port)).symm

theorem shoulders_adjacent_of_triangular {V : Type u}
    (object : FiniteObject V) (center : V)
    (centerHigh : 4 ≤ object.degree center)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3)
    (port : Port object center)
    (triangular : portType object center centerHigh deletionCritical port =
      .triangular) :
    object.graph.Adj
      (firstShoulder object center centerHigh deletionCritical port)
      (secondShoulder object center centerHigh deletionCritical port) := by
  by_contra nonadjacent
  simp [portType, nonadjacent] at triangular

/-- Four-cycle avoidance turns nonadjacent ports at one centre into the exact
fan-compatible shoulder predicate. -/
theorem fanCompatible_of_nonadjacent {V : Type u}
    (object : FiniteObject V) (center : V)
    (fourFree : ¬HasCycleWithLength object.graph HighCenterStructure.FourLength)
    {first second : Port object center} (distinct : first ≠ second)
    (nonadjacent : ¬object.graph.Adj
      (endpoint object center first) (endpoint object center second)) :
    FanCompatible object center first second := by
  have endpointNe : endpoint object center first ≠ endpoint object center second :=
    fun equal => distinct (endpoint_injective object center equal)
  refine ⟨?_, ?_, ?_⟩
  · intro member
    exact nonadjacent (adjacent_of_mem_shoulders object center second member).symm
  · intro member
    exact nonadjacent (adjacent_of_mem_shoulders object center first member)
  · rw [List.disjoint_left]
    intro common commonFirst commonSecond
    exact HighCenterStructure.nonadjacentNeighbors_noCommonOutside fourFree
      endpointNe (ne_center_of_mem_shoulders object center second commonSecond)
      (endpoint_adjacent object center first)
      (endpoint_adjacent object center second)
      (adjacent_of_mem_shoulders object center first commonFirst)
      (adjacent_of_mem_shoulders object center second commonSecond)

/-! ## CT10 classification of one explicit centre fibre -/

def classificationCapability {V : Type u}
    (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit))
    (object : FiniteObject V) (center : V)
    (centerHigh : 4 ≤ object.degree center)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3) :
    CT10.Capability base.problem where
  Datum := Port object center
  Class := PortType
  Promotion := PortType
  classes := portTypes
  classOf := portType object center centerHigh deletionCritical
  Direct := fun _ => False
  directDecidable := fun _ => isFalse id
  promote := id

def classificationInput {V : Type u}
    (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit))
    (object : FiniteObject V) (baseline : base.problem.Baseline object)
    (center : V) (centerHigh : 4 ≤ object.degree center)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3) :
    CT10.Input (classificationCapability base object center centerHigh
      deletionCritical) where
  context := ⟨object, baseline, ()⟩
  data := (ports object center).toOrderedCollection

def classificationRun {V : Type u}
    (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit))
    (object : FiniteObject V) (baseline : base.problem.Baseline object)
    (center : V) (centerHigh : 4 ≤ object.degree center)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3) :=
  CT10.run (classificationCapability base object center centerHigh deletionCritical)
    (classificationInput base object baseline center centerHigh deletionCritical)

def classificationChecks {V : Type u} (object : FiniteObject V)
    (center : V) : Nat := 2 * object.degree center + 2

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
        object.input.vertices.orderedValues.length :=
      List.length_filter_le _ _
    _ = object.input.vertices.card := by
      simp [FinEnum.orderedValues, FinEnum.toList]

theorem classificationChecks_linear {V : Type u} (object : FiniteObject V)
    (center : V) :
    classificationChecks object center ≤ 2 * object.input.vertices.card + 2 := by
  unfold classificationChecks
  have degreeLe := degree_le_vertexCount object center
  omega

private theorem triangular_iff_not_open {V : Type u}
    (object : FiniteObject V) (center : V)
    (centerHigh : 4 ≤ object.degree center)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3)
    (port : Port object center) :
    portType object center centerHigh deletionCritical port = .triangular ↔
      ¬portType object center centerHigh deletionCritical port = .open := by
  cases typeEq : portType object center centerHigh deletionCritical port <;> simp

theorem portType_card_partition {V : Type u}
    (object : FiniteObject V) (center : V)
    (centerHigh : 4 ≤ object.degree center)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3) :
    Fintype.card (OpenPort object center centerHigh deletionCritical) +
        Fintype.card (TriangularPort object center centerHigh deletionCritical) =
      object.degree center := by
  let p : Port object center → Prop := fun port =>
    portType object center centerHigh deletionCritical port = .open
  have triangularCard :
      Fintype.card (TriangularPort object center centerHigh deletionCritical) =
        Fintype.card {port : Port object center // ¬p port} := by
    apply Fintype.card_congr
    exact Equiv.subtypeEquiv (Equiv.refl _) fun port =>
      triangular_iff_not_open object center centerHigh deletionCritical port
  rw [triangularCard, Fintype.card_subtype_compl p]
  rw [Nat.add_sub_of_le (Fintype.card_subtype_le p)]
  simpa [p, FinEnum.card_eq_fintypeCard] using ports_card_eq_degree object center

theorem openPort_card_le_two_of_noCompatible {V : Type u}
    (object : FiniteObject V) (center : V)
    (centerHigh : 4 ≤ object.degree center)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3)
    (fourFree : ¬HasCycleWithLength object.graph HighCenterStructure.FourLength)
    (noCompatible : ¬∃ first second :
      OpenPort object center centerHigh deletionCritical,
      first ≠ second ∧ FanCompatible object center first.1 second.1) :
    Fintype.card (OpenPort object center centerHigh deletionCritical) ≤ 2 := by
  by_contra tooMany
  have three : 2 < Fintype.card
      (OpenPort object center centerHigh deletionCritical) := by omega
  obtain ⟨first, middle, last, firstNeMiddle, firstNeLast, middleNeLast⟩ :=
    Fintype.two_lt_card_iff.mp three
  have pairAdjacent : ∀ {left right :
      OpenPort object center centerHigh deletionCritical}, left ≠ right →
      object.graph.Adj (endpoint object center left.1)
        (endpoint object center right.1) := by
    intro left right leftNeRight
    by_contra nonadjacent
    apply noCompatible
    exact ⟨left, right, leftNeRight,
      fanCompatible_of_nonadjacent object center fourFree
        (fun equal => leftNeRight (Subtype.ext equal)) nonadjacent⟩
  have endpointEq := HighCenterStructure.neighborhood_isMatching fourFree
    (endpoint_adjacent object center first.1)
    (endpoint_adjacent object center middle.1)
    (endpoint_adjacent object center last.1)
    (pairAdjacent firstNeMiddle)
    (pairAdjacent middleNeLast)
  exact firstNeLast (Subtype.ext (endpoint_injective object center endpointEq))

/-- Exact local dichotomy: a compatible open pair, or all but at most two
incident ports are triangular. -/
theorem localDichotomy {V : Type u}
    (object : FiniteObject V) (center : V)
    (centerHigh : 4 ≤ object.degree center)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3)
    (fourFree : ¬HasCycleWithLength object.graph HighCenterStructure.FourLength) :
    (∃ first second : OpenPort object center centerHigh deletionCritical,
      first ≠ second ∧ FanCompatible object center first.1 second.1) ∨
      object.degree center - 2 ≤
        Fintype.card (TriangularPort object center centerHigh deletionCritical) := by
  by_cases compatible : ∃ first second :
      OpenPort object center centerHigh deletionCritical,
      first ≠ second ∧ FanCompatible object center first.1 second.1
  · exact Or.inl compatible
  · right
    have openLe := openPort_card_le_two_of_noCompatible object center centerHigh
      deletionCritical fourFree compatible
    have partition := portType_card_partition object center centerHigh deletionCritical
    omega

structure VerifiedStage {V : Type u}
    (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit))
    (object : FiniteObject V) (baseline : base.problem.Baseline object)
    (center : V) (centerHigh : 4 ≤ object.degree center)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3)
    (fourFree : ¬HasCycleWithLength object.graph HighCenterStructure.FourLength) :
    Prop where
  verified : (classificationRun base object baseline center centerHigh
    deletionCritical).outcome.Valid
  traceValid : CT10.Graph.ValidTrace
    (classificationCapability base object center centerHigh deletionCritical)
    (classificationInput base object baseline center centerHigh deletionCritical)
    (classificationRun base object baseline center centerHigh deletionCritical).trace
  total : ∃ result, result = classificationRun base object baseline center centerHigh
      deletionCritical ∧ result.outcome.Valid
  dichotomy :
    (∃ first second : OpenPort object center centerHigh deletionCritical,
      first ≠ second ∧ FanCompatible object center first.1 second.1) ∨
      object.degree center - 2 ≤
        Fintype.card (TriangularPort object center centerHigh deletionCritical)
  polynomial : classificationChecks object center ≤
    2 * object.input.vertices.card + 2

def verifiedStage {V : Type u}
    (base : MinimumDegreeCycle.StaticInput V (fun _ => Unit))
    (object : FiniteObject V) (baseline : base.problem.Baseline object)
    (center : V) (centerHigh : 4 ≤ object.degree center)
    (deletionCritical : ∀ dart : object.graph.Dart,
      object.degree dart.fst = 3 ∨ object.degree dart.snd = 3)
    (fourFree : ¬HasCycleWithLength object.graph HighCenterStructure.FourLength) :
    VerifiedStage base object baseline center centerHigh deletionCritical fourFree where
  verified := CT10.run_verified _ _
  traceValid := CT10.run_trace_valid _ _
  total := ⟨_, rfl, CT10.run_verified _ _⟩
  dichotomy := localDichotomy object center centerHigh deletionCritical fourFree
  polynomial := classificationChecks_linear object center

end StructuralExhaustion.Graph.HighCenterPort
