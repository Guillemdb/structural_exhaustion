import StructuralExhaustion.Graph.InducedPathColdCorridor
import StructuralExhaustion.Graph.InducedPathColdSkeleton
import StructuralExhaustion.Graph.OrderedBFSTree
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Data.List.Cycle
import Mathlib.Tactic

namespace StructuralExhaustion.Graph.InducedPathComponentBoundarySchedule

open StructuralExhaustion
open InducedPathWindowLedger
open InducedPathColdLedger
open InducedPathColdSkeleton
open scoped Sym2

universe u

variable {V : Type u} {object : FiniteObject V}

theorem next_ne_self_of_nodup_of_two_le {alpha : Type*} [DecidableEq alpha]
    (schedule : List alpha) (anchor : alpha) (nodup : schedule.Nodup)
    (anchorMem : anchor ∈ schedule) (lengthTwo : 2 ≤ schedule.length) :
    schedule.next anchor anchorMem ≠ anchor := by
  intro equal
  have indexLt := List.idxOf_lt_length_iff.mpr anchorMem
  rw [List.next_eq_getElem anchorMem] at equal
  have anchorAt : schedule[schedule.idxOf anchor]'indexLt = anchor :=
    List.getElem_idxOf indexLt
  have nextIndexLt :
      (schedule.idxOf anchor + 1) % schedule.length < schedule.length :=
    Nat.mod_lt _ (by omega)
  have indexEq :
      (schedule.idxOf anchor + 1) % schedule.length = schedule.idxOf anchor := by
    apply (List.Nodup.getElem_inj_iff nodup).mp
    show schedule[(schedule.idxOf anchor + 1) % schedule.length]'nextIndexLt =
      schedule[schedule.idxOf anchor]'indexLt
    simpa [anchorAt] using equal
  by_cases beforeEnd : schedule.idxOf anchor + 1 < schedule.length
  · rw [Nat.mod_eq_of_lt beforeEnd] at indexEq
    omega
  · have endEq : schedule.idxOf anchor + 1 = schedule.length := by omega
    rw [endEq, Nat.mod_self] at indexEq
    omega

/-!
# Boundary schedule of one induced-remainder component

The only path selected here is the deleted-edge return supplied by a proved
non-bridge fact.  A recursive scan of that one path finds an edge leaving the
anchor's outside component.  Since two surviving outside vertices joined by
an ambient edge lie in the same induced component, the other endpoint of the
exit edge belongs to the deleted ambient-cubic window union.  It therefore
defines a second literal boundary stub in the same component.

The finite schedule is the exact ambient-cubic boundary-stub token order,
filtered by incidence with the anchor component.  It is not a cold-family
schedule.  We anchor the stored order at the supplied stub and choose the
literal cyclic next entry, with wrap at the end.  The component path is the
declared-order BFS-tree shortest path; no global lexicographic path-family
scan is claimed.
-/

/-- A walk whose endpoints lie on opposite sides of a predicate contains an
oriented edge leaving that predicate.  This scans only the supplied walk. -/
theorem exists_exit_edge {G : SimpleGraph V} {start finish : V}
    (path : G.Walk start finish) (P : V -> Prop)
    (startIn : P start) (finishOut : ¬P finish) :
    Exists fun inside => Exists fun outside =>
      P inside /\ ¬P outside /\ G.Adj inside outside /\
        s(inside, outside) ∈ path.edges := by
  induction path with
  | nil => exact (finishOut startIn).elim
  | @cons first second last adjacent tail ih =>
      by_cases secondIn : P second
      · obtain ⟨inside, outside, insideIn, outsideOut, edge, member⟩ :=
          ih secondIn finishOut
        exact ⟨inside, outside, insideIn, outsideOut, edge, by simp [member]⟩
      · exact ⟨first, second, startIn, secondIn, adjacent, by simp⟩

/-- Proof-carrying prefix form of the same one-walk scan. -/
structure ExitCertificate {G : SimpleGraph V} {start finish : V}
    (path : G.Walk start finish) (P : V -> Prop) where
  inside : V
  outside : V
  prefixWalk : G.Walk start inside
  prefixEdges : (prefixWalk.edges <+: path.edges)
  prefixInside : ∀ vertex ∈ prefixWalk.support, P vertex
  insideIn : P inside
  outsideOut : ¬P outside
  adjacent : G.Adj inside outside
  edgeMember : s(inside, outside) ∈ path.edges

noncomputable def scanExit {G : SimpleGraph V} {start finish : V}
    (path : G.Walk start finish) (P : V -> Prop)
    (startIn : P start) (finishOut : ¬P finish) :
    ExitCertificate path P := by
  induction path with
  | nil => exact (finishOut startIn).elim
  | @cons first second last adjacent tail ih =>
      by_cases secondIn : P second
      · let certificate := ih secondIn finishOut
        exact {
          inside := certificate.inside
          outside := certificate.outside
          prefixWalk := .cons adjacent certificate.prefixWalk
          prefixEdges := by
            exact List.cons_prefix_cons.mpr ⟨rfl, certificate.prefixEdges⟩
          prefixInside := by
            intro vertex member
            simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at member
            exact member.elim (fun equal => equal ▸ startIn)
              (fun tailMember => certificate.prefixInside vertex tailMember)
          insideIn := certificate.insideIn
          outsideOut := certificate.outsideOut
          adjacent := certificate.adjacent
          edgeMember := by simp [certificate.edgeMember]
        }
      · exact {
          inside := first
          outside := second
          prefixWalk := .nil
          prefixEdges := by simp
          prefixInside := by simpa
          insideIn := startIn
          outsideOut := secondIn
          adjacent := adjacent
          edgeMember := by simp
        }

/-- Exact graph data needed to construct the component boundary schedule. -/
structure Input (object : FiniteObject V) where
  anchor : BoundaryStub object
  notBridge : ¬object.graph.IsBridge
    (InducedPathColdCorridor.CubicStub.dart
      { token := anchor.token, cubic := anchor.cubic }).edge

/-- One executable BFS in the outside graph, rooted at the anchor endpoint. -/
noncomputable def outsideBfsProfile (input : Input object) :
    OrderedBFSTree.Profile (outsideObject object) where
  root := input.anchor.endpoint

/-- The single stored outside-component carrier used by every later scan. -/
noncomputable def componentVertices (input : Input object) :
    Finset (OutsideVertex object) :=
  (outsideBfsProfile input).discovered
    (outsideObject object).input.vertices.card

/-- Semantic validation of the one computed BFS carrier. -/
theorem mem_componentVertices_iff (input : Input object)
    (vertex : OutsideVertex object) :
    vertex ∈ componentVertices input ↔
      (outsideObject object).graph.connectedComponentMk vertex =
        component input.anchor := by
  let profile := outsideBfsProfile input
  let outside := outsideObject object
  constructor
  · intro member
    obtain ⟨walk, _bound⟩ :=
      (profile.discovered_iff_bounded_walk outside.input.vertices.card vertex).mp
        member
    exact (SimpleGraph.ConnectedComponent.sound ⟨walk⟩).symm
  · intro equal
    have reachable : outside.graph.Reachable profile.root vertex := by
      apply SimpleGraph.ConnectedComponent.exact
      simpa [profile, outsideBfsProfile, component] using equal.symm
    exact reachable.elim_path fun path =>
      (profile.discovered_iff_bounded_walk outside.input.vertices.card vertex).mpr
        ⟨path, by
          letI : FinEnum (OutsideVertex object) := outside.input.vertices
          simpa [FinEnum.card_eq_fintypeCard] using path.property.length_lt.le⟩

namespace Input

variable (input : Input object)

noncomputable def cubicStub : InducedPathColdCorridor.CubicStub object where
  token := input.anchor.token
  cubic := input.anchor.cubic

noncomputable def returnPath : DartReturn object.graph input.cubicStub.dart :=
  DartReturn.ofNotBridge input.notBridge

noncomputable def ambientReturn : object.graph.Walk input.anchor.neighbor
    (selectedWindow object input.anchor.window input.anchor.offset) :=
  input.returnPath.path.mapLe
    (object.graph.deleteEdges_le {input.cubicStub.dart.edge})

theorem ambientReturn_isPath : input.ambientReturn.IsPath :=
  input.returnPath.isPath.mapLe _

theorem root_not_mem_ambientReturn :
    input.cubicStub.dart.edge ∉ input.ambientReturn.edges := by
  let unrestricted := input.returnPath.toEdgeRootedReturn
  exact unrestricted.root_not_mem_path

def InAnchorComponent (vertex : V) : Prop :=
  ∃ outside : vertex ∈ outsideVertices object,
    (⟨vertex, outside⟩ : OutsideVertex object) ∈ componentVertices input

noncomputable def inAnchorComponentDecidable (vertex : V) :
    Decidable (input.InAnchorComponent vertex) := by
  letI : DecidableEq V := object.input.vertices.decEq
  unfold InAnchorComponent
  infer_instance

theorem anchor_in_component : input.InAnchorComponent input.anchor.neighbor := by
  refine ⟨input.anchor.outside, ?_⟩
  rw [mem_componentVertices_iff]
  rfl

theorem window_vertex_not_in_component :
    ¬input.InAnchorComponent
      (selectedWindow object input.anchor.window input.anchor.offset) := by
  rintro ⟨outside, _member⟩
  letI : DecidableEq V := object.input.vertices.decEq
  have deleted : selectedWindow object input.anchor.window input.anchor.offset ∈
      deletedWindowVertices object := by
    classical
    simp only [deletedWindowVertices, Finset.mem_biUnion]
    refine ⟨input.anchor.window, Finset.mem_univ _, ?_⟩
    simp [input.anchor.cubic, InducedPathPacking.mem_support_iff]
  exact (Finset.mem_sdiff.mp outside).2 deleted

/-- The exact first component-exit certificate on the one deleted-edge
return.  Every retained prefix vertex is still in the anchor component. -/
noncomputable def exitCertificate :
    ExitCertificate input.ambientReturn input.InAnchorComponent :=
  scanExit input.ambientReturn input.InAnchorComponent
    input.anchor_in_component input.window_vertex_not_in_component

noncomputable abbrev outsideEndpoint : V := input.exitCertificate.inside
noncomputable abbrev insideEndpoint : V := input.exitCertificate.outside

theorem exitPrefix_inside : ∀ vertex ∈ input.exitCertificate.prefixWalk.support,
    input.InAnchorComponent vertex :=
  input.exitCertificate.prefixInside

theorem outsideEndpoint_outside :
    input.outsideEndpoint ∈ outsideVertices object :=
  input.exitCertificate.insideIn.choose

theorem outsideEndpoint_component :
    (⟨input.outsideEndpoint, input.outsideEndpoint_outside⟩ :
      OutsideVertex object) ∈ (component input.anchor).supp := by
  rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
  exact (mem_componentVertices_iff input _).mp
    input.exitCertificate.insideIn.choose_spec

theorem insideEndpoint_not_outside :
    input.insideEndpoint ∉ outsideVertices object := by
  intro insideOutside
  have inducedAdjacent : (outsideObject object).graph.Adj
      (⟨input.outsideEndpoint, input.outsideEndpoint_outside⟩ :
        OutsideVertex object)
      (⟨input.insideEndpoint, insideOutside⟩ : OutsideVertex object) :=
    input.exitCertificate.adjacent
  have sameMembership := SimpleGraph.ConnectedComponent.mem_supp_congr_adj
    (component input.anchor) inducedAdjacent
  apply input.exitCertificate.outsideOut
  refine ⟨insideOutside, ?_⟩
  apply (mem_componentVertices_iff input _).mpr
  exact (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mp
    (sameMembership.mp input.outsideEndpoint_component)

theorem insideEndpoint_deleted :
    input.insideEndpoint ∈ deletedWindowVertices object := by
  letI : DecidableEq V := object.input.vertices.decEq
  have ambient := object.mem_vertexFinset input.insideEndpoint
  by_contra notDeleted
  apply input.insideEndpoint_not_outside
  rw [outsideVertices, Finset.mem_sdiff]
  exact ⟨ambient, notDeleted⟩

abbrev Slot := WindowIndex object × Fin 13

@[implicit_reducible] noncomputable def slots : FinEnum (Slot (object := object)) := by
  letI : FinEnum (WindowIndex object) := windowIndices object
  exact inferInstance

def SlotPredicate (slot : Slot (object := object)) : Prop :=
  AmbientCubic object slot.1 /\
    selectedWindow object slot.1 slot.2 = input.insideEndpoint

noncomputable def slotPredicateDecidable (slot : Slot (object := object)) :
    Decidable (input.SlotPredicate slot) := by
  letI : DecidableEq V := object.input.vertices.decEq
  unfold SlotPredicate
  exact @instDecidableAnd _ _ (ambientCubicDecidable object slot.1)
    (object.input.vertices.decEq
      (selectedWindow object slot.1 slot.2) input.insideEndpoint)

/-- Exact finite first search over `WindowIndex × Fin 13`. -/
noncomputable def slotScan := Core.FiniteSearch.first (slots (object := object))
  input.SlotPredicate input.slotPredicateDecidable

theorem exists_slot : ∃ slot : Slot (object := object),
    input.SlotPredicate slot := by
  have member := input.insideEndpoint_deleted
  simp only [deletedWindowVertices, Finset.mem_biUnion] at member
  rcases member with ⟨window, _windowMem, member⟩
  by_cases cubic : AmbientCubic object window
  · simp only [cubic, if_pos, InducedPathPacking.mem_support_iff] at member
    rcases member with ⟨position, equal⟩
    exact ⟨(window, position), cubic, equal⟩
  · simp [cubic] at member

theorem slotScan_absent_false
    (none : ∀ value, value ∈ (slots (object := object)).orderedValues →
      ¬input.SlotPredicate value) : False := by
  rcases input.exists_slot with ⟨slot, holds⟩
  exact none slot ((slots (object := object)).mem_orderedValues slot) holds

theorem slotScan_hasHit : ∃ hit, input.slotScan = .found hit := by
  cases equation : input.slotScan with
  | found hit => exact ⟨hit, rfl⟩
  | absent none => exact (input.slotScan_absent_false none).elim

noncomputable def selectedSlotHit : Core.FiniteSearch.FirstHit
    (slots (object := object)).orderedValues input.SlotPredicate :=
  Classical.choose input.slotScan_hasHit

theorem slotScan_eq_found_selectedSlotHit :
    input.slotScan = .found input.selectedSlotHit :=
  Classical.choose_spec input.slotScan_hasHit

/-- Extract the first selected ambient-cubic window position at the inside
end from the explicit finite slot scan. -/
noncomputable def windowPosition :
    {entry : WindowIndex object × Fin 13 //
      AmbientCubic object entry.1 /\
      selectedWindow object entry.1 entry.2 = input.insideEndpoint} :=
  ⟨input.selectedSlotHit.value, input.selectedSlotHit.holds⟩

/-- Provenance of the executable first slot: the retained position is exactly
the first hit and its prefix carries the no-earlier-slot theorem. -/
theorem windowPosition_firstHit :
    ∃ hit, input.slotScan = .found hit ∧
      input.windowPosition.1 = hit.value ∧
      ∀ candidate ∈ hit.before, ¬input.SlotPredicate candidate := by
  exact ⟨input.selectedSlotHit, input.slotScan_eq_found_selectedSlotHit,
    rfl, input.selectedSlotHit.beforeAbsent⟩

theorem outsideEndpoint_external :
    input.outsideEndpoint ∈ externalNeighbors object
      input.windowPosition.1.1 input.windowPosition.1.2 := by
  classical
  letI : FinEnum V := object.input.vertices
  letI : DecidableEq V := object.input.vertices.decEq
  letI : DecidableRel object.graph.Adj := object.input.decideAdj
  rw [externalNeighbors, Finset.mem_sdiff]
  constructor
  · rw [ambientNeighbors, SimpleGraph.mem_neighborFinset,
      input.windowPosition.2.2]
    exact input.exitCertificate.adjacent.symm
  · intro internal
    apply (Finset.mem_sdiff.mp input.outsideEndpoint_outside).2
    simp only [deletedWindowVertices, Finset.mem_biUnion]
    refine ⟨input.windowPosition.1.1, Finset.mem_univ _, ?_⟩
    simp only [input.windowPosition.2.1, if_pos,
      InducedPathPacking.mem_support_iff]
    unfold internalNeighbors at internal
    rw [Finset.mem_image] at internal
    rcases internal with ⟨position, _positionMem, equal⟩
    exact ⟨position, equal⟩

noncomputable def secondStub : BoundaryStub object where
  token := ⟨input.windowPosition.1.1, input.windowPosition.1.2,
    ⟨input.outsideEndpoint, input.outsideEndpoint_external⟩⟩
  cubic := input.windowPosition.2.1
  outside := input.outsideEndpoint_outside

theorem second_same_component :
    component input.secondStub = component input.anchor := by
  exact input.outsideEndpoint_component

theorem second_distinct : input.secondStub ≠ input.anchor := by
  intro equal
  have rootEq : input.cubicStub.dart.edge =
      s(input.insideEndpoint, input.outsideEndpoint) := by
    change s(selectedWindow object input.anchor.window input.anchor.offset,
      input.anchor.neighbor) = _
    have windowEq := congrArg BoundaryStub.window equal
    have offsetEq := congrArg BoundaryStub.offset equal
    have neighborEq := congrArg BoundaryStub.neighbor equal
    rw [← input.windowPosition.2.2]
    change s(selectedWindow object input.anchor.window input.anchor.offset,
      input.anchor.neighbor) =
      s(selectedWindow object input.secondStub.window input.secondStub.offset,
        input.secondStub.neighbor)
    rw [windowEq.symm, offsetEq.symm, neighborEq.symm]
  apply input.root_not_mem_ambientReturn
  rw [rootEq, Sym2.eq_swap]
  exact input.exitCertificate.edgeMember

end Input

/-! ## Exact finite incident-stub schedule -/

@[reducible] noncomputable def boundaryStubs (object : FiniteObject V) :
    FinEnum (BoundaryStub object) := by
  classical
  let predicate := fun token : Token object =>
    AmbientCubic object token.1 /\ token.2.2.1 ∈ outsideVertices object
  let accepted := Core.Enumeration.subtype (tokens object) predicate (by
    intro token
    exact instDecidableAnd)
  letI := accepted
  exact FinEnum.ofEquiv
    {token : Token object // predicate token}
    { toFun := fun stub => ⟨stub.token, stub.cubic, stub.outside⟩
      invFun := fun token => ⟨token.1, token.2.1, token.2.2⟩
      left_inv := by intro stub; cases stub; rfl
      right_inv := by intro token; cases token; rfl }

noncomputable def incidentStubs (input : Input object) : List (BoundaryStub object) := by
  classical
  exact (boundaryStubs object).orderedValues.filter
    (fun stub => stub.endpoint ∈ componentVertices input)

theorem anchor_mem_incidentStubs (input : Input object) :
    input.anchor ∈ incidentStubs input := by
  classical
  simp [incidentStubs, FinEnum.mem_orderedValues,
    mem_componentVertices_iff, component]

theorem second_mem_incidentStubs (input : Input object) :
    input.secondStub ∈ incidentStubs input := by
  classical
  rw [incidentStubs, List.mem_filter]
  constructor
  · exact (boundaryStubs object).mem_orderedValues input.secondStub
  · apply decide_eq_true
    rw [mem_componentVertices_iff]
    change component input.secondStub = component input.anchor
    exact input.second_same_component

theorem mem_incidentStubs_iff (input : Input object)
    (stub : BoundaryStub object) :
    stub ∈ incidentStubs input ↔ component stub = component input.anchor := by
  classical
  rw [incidentStubs, List.mem_filter]
  simp only [FinEnum.mem_orderedValues, true_and]
  constructor
  · intro selected
    have member : stub.endpoint ∈ componentVertices input :=
      of_decide_eq_true selected
    exact (mem_componentVertices_iff input stub.endpoint).mp member
  · intro same
    exact decide_eq_true
      ((mem_componentVertices_iff input stub.endpoint).mpr same)

theorem incidentStubs_nodup (input : Input object) :
    (incidentStubs input).Nodup := by
  classical
  exact List.Nodup.filter _ (boundaryStubs object).nodup_orderedValues

theorem two_le_incidentStubs_length (input : Input object) :
    2 ≤ (incidentStubs input).length := by
  classical
  have anchorMem := anchor_mem_incidentStubs input
  have secondMem := second_mem_incidentStubs input
  have distinct := input.second_distinct
  cases equation : incidentStubs input with
  | nil => simp [equation] at anchorMem
  | cons first tail =>
      cases tail with
      | nil =>
          simp [equation] at anchorMem secondMem
          exact (distinct (secondMem.trans anchorMem.symm)).elim
      | cons next rest => simp

/-- Literal cyclic successor in the exact stored incident-stub order. -/
noncomputable def successor (input : Input object) : BoundaryStub object :=
  by
    exact @List.next _ (boundaryStubs object).decEq
      (incidentStubs input) input.anchor
      (anchor_mem_incidentStubs input)

theorem successor_mem (input : Input object) :
    successor input ∈ incidentStubs input := by
  letI : DecidableEq (BoundaryStub object) := (boundaryStubs object).decEq
  unfold successor
  exact List.next_mem _ _ _

theorem successor_distinct (input : Input object) :
    successor input ≠ input.anchor := by
  letI : DecidableEq (BoundaryStub object) := (boundaryStubs object).decEq
  exact next_ne_self_of_nodup_of_two_le (incidentStubs input) input.anchor
    (incidentStubs_nodup input) (anchor_mem_incidentStubs input)
      (two_le_incidentStubs_length input)

theorem successor_same_component (input : Input object) :
    component (successor input) = component input.anchor := by
  classical
  have member := successor_mem input
  exact (mem_incidentStubs_iff input _).mp member

/-- The exact declared successor relation owned by this stored schedule. -/
noncomputable def DeclaredSuccessor (input : Input object)
    (anchor next : BoundaryStub object) : Prop :=
  anchor = input.anchor /\ next = successor input

noncomputable def twoStubComponent (input : Input object) :
    TwoStubComponent object (DeclaredSuccessor input) where
  anchor := input.anchor
  successor := successor input
  distinct := successor_distinct input
  sameComponent := successor_same_component input
  declaredSuccessor := ⟨rfl, rfl⟩

/-- Finite component object with the exact outside-vertex order restricted to
the returned component. -/
noncomputable def componentObject (input : Input object) :
    FiniteObject (component input.anchor).supp where
  graph := (component input.anchor).toSimpleGraph
  input := {
    vertices := by
      let outside := outsideObject object
      letI : FinEnum (OutsideVertex object) := outside.input.vertices
      let accepted := Core.Enumeration.subtype outside.input.vertices
        (fun vertex => vertex ∈ componentVertices input)
        (fun _vertex => inferInstance)
      letI := accepted
      exact FinEnum.ofEquiv
        {vertex : OutsideVertex object // vertex ∈ componentVertices input}
        { toFun := fun vertex => ⟨vertex.1,
            (mem_componentVertices_iff input vertex.1).mpr vertex.2⟩
          invFun := fun vertex => ⟨vertex.1,
            (mem_componentVertices_iff input vertex.1).mp vertex.2⟩
          left_inv := by intro vertex; apply Subtype.ext; rfl
          right_inv := by intro vertex; apply Subtype.ext; rfl }
    decideAdj := by
      let outside := outsideObject object
      letI : DecidableRel outside.graph.Adj := outside.input.decideAdj
      exact fun left right => outside.input.decideAdj left.1 right.1
  }

/-- Declared-order BFS rooted at the anchor endpoint. -/
noncomputable def bfsProfile (input : Input object) :
    OrderedBFSTree.Profile (componentObject input) where
  root := (twoStubComponent input).componentRoot

/-- Executable declared-order BFS-tree shortest path.  This is deterministic
under the stored outside-vertex order, but is not claimed globally lex-first. -/
noncomputable def componentPath (input : Input object) :=
  (bfsProfile input).treeWalk
    (twoStubComponent input).component_preconnected
    (twoStubComponent input).componentTarget

theorem componentPath_isPath (input : Input object) :
    (componentPath input).IsPath :=
  (bfsProfile input).treeWalk_isPath
    (twoStubComponent input).component_preconnected _

theorem componentPath_shortest (input : Input object) :
    (componentPath input).length =
      (component input.anchor).toSimpleGraph.dist
        (twoStubComponent input).componentRoot
        (twoStubComponent input).componentTarget :=
  (bfsProfile input).treeWalk_shortest
    (twoStubComponent input).component_preconnected _

/-- Stub-filter work after the window degree table and one outside-component
BFS have been computed.  Every actual token performs one cubic flag lookup,
one deleted-union lookup, and one membership lookup in the stored component
finset. -/
noncomputable def stubFilterChecks (_input : Input object) : Nat :=
  (tokens object).card *
    (2 + 13 * packingNumber object +
      (outsideObject object).input.vertices.card)

/-- Full visible finite work: the window ledger, explicit slot scan, the one
deleted-edge-return scan with a linear stored-finset lookup at every stage,
one outside BFS used by every component filter, one outside-carrier scan with
linear lookup to build the component object, the actual token filter, and the
declared-order BFS inside the retained component. -/
noncomputable def visibleChecks (input : Input object) : Nat :=
  InducedPathWindowLedger.checks object +
    13 * packingNumber object +
    input.ambientReturn.length *
      (outsideObject object).input.vertices.card +
    (outsideBfsProfile input).budget
      (outsideObject object).input.vertices.card +
    (outsideObject object).input.vertices.card ^ 2 +
    stubFilterChecks input +
    (bfsProfile input).budget (componentObject input).input.vertices.card

theorem visibleChecks_eq (input : Input object) :
    visibleChecks input = InducedPathWindowLedger.checks object +
      13 * packingNumber object +
      input.ambientReturn.length *
        (outsideObject object).input.vertices.card +
      (outsideBfsProfile input).budget
        (outsideObject object).input.vertices.card +
      (outsideObject object).input.vertices.card ^ 2 +
      (tokens object).card *
        (2 + 13 * packingNumber object +
          (outsideObject object).input.vertices.card) +
      (bfsProfile input).budget (componentObject input).input.vertices.card := rfl

theorem bfsBudget_polynomial (input : Input object) :
    (bfsProfile input).budget (componentObject input).input.vertices.card ≤
      1 + (componentObject input).input.vertices.card *
        ((componentObject input).input.vertices.card *
          ((componentObject input).input.vertices.card + 1)) :=
  (bfsProfile input).budget_polynomial _

theorem outsideBfsBudget_polynomial (input : Input object) :
    (outsideBfsProfile input).budget
        (outsideObject object).input.vertices.card ≤
      1 + (outsideObject object).input.vertices.card *
        ((outsideObject object).input.vertices.card *
          ((outsideObject object).input.vertices.card + 1)) :=
  (outsideBfsProfile input).budget_polynomial _

/-- One scalar dominating every explicitly scanned local collection. -/
noncomputable def localScale (input : Input object) : Nat :=
  1 + object.input.vertices.card + packingNumber object +
    (tokens object).card + (outsideObject object).input.vertices.card +
    (componentObject input).input.vertices.card + input.ambientReturn.length

/-- Complete polynomial bound for the full visible ledger.  The scale is the
sum of the sizes of the actual local schedules; no graph, coloring, context,
or path family is enumerated. -/
theorem visibleChecks_polynomial (input : Input object) :
    visibleChecks input ≤ 50 * localScale input ^ 3 := by
  let scale := localScale input
  change visibleChecks input ≤ 50 * scale ^ 3
  have scalePos : 1 ≤ scale := by
    dsimp [scale, localScale]
    omega
  have vertexLe : object.input.vertices.card ≤ scale := by
    dsimp [scale, localScale]
    omega
  have packingLe : packingNumber object ≤ scale := by
    dsimp [scale, localScale]
    omega
  have tokenLe : (tokens object).card ≤ scale := by
    dsimp [scale, localScale]
    omega
  have outsideLe : (outsideObject object).input.vertices.card ≤ scale := by
    dsimp [scale, localScale]
    omega
  have componentLe : (componentObject input).input.vertices.card ≤ scale := by
    dsimp [scale, localScale]
    omega
  have returnLe : input.ambientReturn.length ≤ scale := by
    dsimp [scale, localScale]
    omega
  have outsideBudget := outsideBfsBudget_polynomial input
  have componentBudget := bfsBudget_polynomial input
  have windowBound :
      packingNumber object * (13 * object.input.vertices.card) ≤
        scale * (13 * scale) :=
    Nat.mul_le_mul packingLe (Nat.mul_le_mul_left 13 vertexLe)
  have filterFactor :
      2 + 13 * packingNumber object +
          (outsideObject object).input.vertices.card ≤ 2 + 14 * scale := by
    nlinarith
  have filterBound :
      (tokens object).card *
          (2 + 13 * packingNumber object +
            (outsideObject object).input.vertices.card) ≤
        scale * (2 + 14 * scale) :=
    Nat.mul_le_mul tokenLe filterFactor
  have returnScanBound :
      input.ambientReturn.length *
          (outsideObject object).input.vertices.card ≤ scale * scale :=
    Nat.mul_le_mul returnLe outsideLe
  have componentFilterBound :
      (outsideObject object).input.vertices.card ^ 2 ≤ scale ^ 2 := by
    exact Nat.pow_le_pow_left outsideLe 2
  have outsideCube :
      (outsideObject object).input.vertices.card *
          ((outsideObject object).input.vertices.card *
            ((outsideObject object).input.vertices.card + 1)) ≤
        scale * (scale * (scale + 1)) :=
    Nat.mul_le_mul outsideLe
      (Nat.mul_le_mul outsideLe (Nat.add_le_add_right outsideLe 1))
  have componentCube :
      (componentObject input).input.vertices.card *
          ((componentObject input).input.vertices.card *
            ((componentObject input).input.vertices.card + 1)) ≤
        scale * (scale * (scale + 1)) :=
    Nat.mul_le_mul componentLe
      (Nat.mul_le_mul componentLe (Nat.add_le_add_right componentLe 1))
  have outsideBudget' :
      (outsideBfsProfile input).budget
          (outsideObject object).input.vertices.card ≤
        1 + scale * (scale * (scale + 1)) :=
    outsideBudget.trans (Nat.add_le_add_left outsideCube 1)
  have componentBudget' :
      (bfsProfile input).budget (componentObject input).input.vertices.card ≤
        1 + scale * (scale * (scale + 1)) :=
    componentBudget.trans (Nat.add_le_add_left componentCube 1)
  rw [visibleChecks_eq]
  unfold InducedPathWindowLedger.checks
  calc
    _ ≤ scale * (13 * scale) + 13 * scale + scale * scale +
          (1 + scale * (scale * (scale + 1))) +
          scale ^ 2 +
          scale * (2 + 14 * scale) +
          (1 + scale * (scale * (scale + 1))) := by omega
    _ ≤ 50 * scale ^ 3 := by
      ring_nf
      nlinarith [Nat.mul_self_le_mul_self scalePos]

end StructuralExhaustion.Graph.InducedPathComponentBoundarySchedule
