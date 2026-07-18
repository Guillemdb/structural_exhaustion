import StructuralExhaustion.Graph.InducedPathComponentBoundarySchedule
import StructuralExhaustion.Graph.InducedPathRestrictedColdSkeleton

namespace StructuralExhaustion.Graph.InducedPathRestrictedComponentBoundarySchedule

open StructuralExhaustion
open InducedPathWindowLedger
open InducedPathColdLedger
open InducedPathColdCorridor
open InducedPathRestrictedColdSkeleton
open scoped Sym2

universe u

variable {V : Type u} {object : FiniteObject V}
variable {family : CubicWindowFamily object}

/-!
# Boundary schedule in an explicit restricted cold-window remainder

Every object in this file is parameterized by one `CubicWindowFamily`.
Consequently the anchor, component carrier, incident-stub schedule, cyclic
successor, component object and both BFS runs live in the identical restricted
outside graph.  No path or successor is accepted from a caller.
-/

/-- Exact input obtained from the restricted endpoint split. -/
structure Input (family : CubicWindowFamily object) where
  anchor : BoundaryStub family
  notBridge : ¬object.graph.IsBridge
    (CubicStub.dart { token := anchor.token, cubic := anchor.cubic }).edge

noncomputable def outsideBfsProfile (input : Input family) :
    OrderedBFSTree.Profile (outsideObject family) where
  root := input.anchor.endpoint

noncomputable def componentVertices (input : Input family) :
    Finset (OutsideVertex family) :=
  (outsideBfsProfile input).discovered
    (outsideObject family).input.vertices.card

theorem mem_componentVertices_iff (input : Input family)
    (vertex : OutsideVertex family) :
    vertex ∈ componentVertices input ↔
      (outsideObject family).graph.connectedComponentMk vertex =
        component input.anchor := by
  let profile := outsideBfsProfile input
  let outside := outsideObject family
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
          letI : FinEnum (OutsideVertex family) := outside.input.vertices
          simpa [FinEnum.card_eq_fintypeCard] using path.property.length_lt.le⟩

namespace Input

variable (input : Input family)

noncomputable def cubicStub : CubicStub object where
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
  exact input.returnPath.toEdgeRootedReturn.root_not_mem_path

def InAnchorComponent (vertex : V) : Prop :=
  ∃ outside : vertex ∈ outsideVertices family,
    (⟨vertex, outside⟩ : OutsideVertex family) ∈ componentVertices input

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
      deletedWindowVertices family := by
    classical
    simp only [deletedWindowVertices, Finset.mem_biUnion]
    refine ⟨input.anchor.window, input.anchor.window_mem, ?_⟩
    exact (InducedPathPacking.mem_support_iff object 13
      (selectedWindow object input.anchor.window) _).2
      ⟨input.anchor.offset, rfl⟩
  exact (Finset.mem_sdiff.mp outside).2 deleted

noncomputable def exitCertificate :=
  InducedPathComponentBoundarySchedule.scanExit input.ambientReturn
    input.InAnchorComponent input.anchor_in_component
    input.window_vertex_not_in_component

noncomputable abbrev outsideEndpoint : V := input.exitCertificate.inside
noncomputable abbrev insideEndpoint : V := input.exitCertificate.outside

theorem outsideEndpoint_outside :
    input.outsideEndpoint ∈ outsideVertices family :=
  input.exitCertificate.insideIn.choose

theorem outsideEndpoint_component :
    (⟨input.outsideEndpoint, input.outsideEndpoint_outside⟩ :
      OutsideVertex family) ∈ (component input.anchor).supp := by
  rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
  exact (mem_componentVertices_iff input _).mp
    input.exitCertificate.insideIn.choose_spec

theorem insideEndpoint_not_outside :
    input.insideEndpoint ∉ outsideVertices family := by
  intro insideOutside
  have inducedAdjacent : (outsideObject family).graph.Adj
      (⟨input.outsideEndpoint, input.outsideEndpoint_outside⟩ :
        OutsideVertex family)
      (⟨input.insideEndpoint, insideOutside⟩ : OutsideVertex family) :=
    input.exitCertificate.adjacent
  have sameMembership := SimpleGraph.ConnectedComponent.mem_supp_congr_adj
    (component input.anchor) inducedAdjacent
  apply input.exitCertificate.outsideOut
  refine ⟨insideOutside, ?_⟩
  apply (mem_componentVertices_iff input _).mpr
  exact (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mp
    (sameMembership.mp input.outsideEndpoint_component)

theorem insideEndpoint_deleted :
    input.insideEndpoint ∈ deletedWindowVertices family := by
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
  slot.1 ∈ family.windows ∧
    selectedWindow object slot.1 slot.2 = input.insideEndpoint

noncomputable def slotPredicateDecidable (slot : Slot (object := object)) :
    Decidable (input.SlotPredicate slot) := by
  letI : DecidableEq V := object.input.vertices.decEq
  unfold SlotPredicate
  infer_instance

noncomputable def slotScan := Core.FiniteSearch.first (slots (object := object))
  input.SlotPredicate input.slotPredicateDecidable

theorem exists_slot : ∃ slot : Slot (object := object), input.SlotPredicate slot := by
  have member := input.insideEndpoint_deleted
  simp only [deletedWindowVertices, Finset.mem_biUnion] at member
  rcases member with ⟨window, windowMem, supportMem⟩
  rw [InducedPathPacking.mem_support_iff] at supportMem
  rcases supportMem with ⟨position, equal⟩
  exact ⟨(window, position), windowMem, equal⟩

theorem slotScan_absent_false
    (none : ∀ value, value ∈ (slots (object := object)).orderedValues →
      ¬input.SlotPredicate value) : False := by
  rcases input.exists_slot with ⟨slot, holds⟩
  exact none slot ((slots (object := object)).mem_orderedValues slot) holds

theorem slotScan_hasHit : ∃ hit, input.slotScan = .found hit := by
  cases equation : input.slotScan with
  | found hit => exact ⟨hit, rfl⟩
  | absent none => exact (input.slotScan_absent_false none).elim

noncomputable def selectedSlotHit := Classical.choose input.slotScan_hasHit

theorem slotScan_eq_found_selectedSlotHit :
    input.slotScan = .found input.selectedSlotHit :=
  Classical.choose_spec input.slotScan_hasHit

noncomputable def windowPosition :
    {entry : WindowIndex object × Fin 13 //
      entry.1 ∈ family.windows ∧
      selectedWindow object entry.1 entry.2 = input.insideEndpoint} :=
  ⟨input.selectedSlotHit.value, input.selectedSlotHit.holds⟩

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
    refine ⟨input.windowPosition.1.1, input.windowPosition.2.1, ?_⟩
    rw [InducedPathPacking.mem_support_iff]
    unfold internalNeighbors at internal
    rw [Finset.mem_image] at internal
    rcases internal with ⟨position, _positionMem, equal⟩
    exact ⟨position, equal⟩

noncomputable def secondStub : BoundaryStub family where
  token := ⟨input.windowPosition.1.1, input.windowPosition.1.2,
    ⟨input.outsideEndpoint, input.outsideEndpoint_external⟩⟩
  window_mem := input.windowPosition.2.1
  outside := input.outsideEndpoint_outside

theorem second_same_component :
    component input.secondStub = component input.anchor :=
  input.outsideEndpoint_component

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

@[reducible] noncomputable def boundaryStubs
    (family : CubicWindowFamily object) : FinEnum (BoundaryStub family) := by
  classical
  let predicate := fun token : Token object =>
    token.1 ∈ family.windows ∧ token.2.2.1 ∈ outsideVertices family
  let accepted := Core.Enumeration.subtype (tokens object) predicate (by
    intro token; infer_instance)
  letI := accepted
  exact FinEnum.ofEquiv
    {token : Token object // predicate token}
    { toFun := fun stub => ⟨stub.token, stub.window_mem, stub.outside⟩
      invFun := fun token => ⟨token.1, token.2.1, token.2.2⟩
      left_inv := by intro stub; cases stub; rfl
      right_inv := by intro token; cases token; rfl }

noncomputable def incidentStubs (input : Input family) :
    List (BoundaryStub family) := by
  classical
  exact (boundaryStubs family).orderedValues.filter
    (fun stub => stub.endpoint ∈ componentVertices input)

theorem anchor_mem_incidentStubs (input : Input family) :
    input.anchor ∈ incidentStubs input := by
  classical
  simp [incidentStubs, FinEnum.mem_orderedValues,
    mem_componentVertices_iff, component]

theorem second_mem_incidentStubs (input : Input family) :
    input.secondStub ∈ incidentStubs input := by
  classical
  rw [incidentStubs, List.mem_filter]
  exact ⟨(boundaryStubs family).mem_orderedValues input.secondStub,
    decide_eq_true ((mem_componentVertices_iff input _).mpr
      input.second_same_component)⟩

theorem mem_incidentStubs_iff (input : Input family)
    (stub : BoundaryStub family) :
    stub ∈ incidentStubs input ↔ component stub = component input.anchor := by
  classical
  rw [incidentStubs, List.mem_filter]
  simp only [FinEnum.mem_orderedValues, true_and]
  constructor
  · intro selected
    exact (mem_componentVertices_iff input stub.endpoint).mp
      (of_decide_eq_true selected)
  · intro same
    exact decide_eq_true ((mem_componentVertices_iff input stub.endpoint).mpr same)

theorem incidentStubs_nodup (input : Input family) :
    (incidentStubs input).Nodup := by
  classical
  exact List.Nodup.filter _ (boundaryStubs family).nodup_orderedValues

theorem two_le_incidentStubs_length (input : Input family) :
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

noncomputable def successor (input : Input family) : BoundaryStub family := by
  exact @List.next _ (boundaryStubs family).decEq
    (incidentStubs input) input.anchor (anchor_mem_incidentStubs input)

theorem successor_mem (input : Input family) :
    successor input ∈ incidentStubs input := by
  letI : DecidableEq (BoundaryStub family) := (boundaryStubs family).decEq
  exact List.next_mem _ _ _

theorem successor_distinct (input : Input family) :
    successor input ≠ input.anchor := by
  letI : DecidableEq (BoundaryStub family) := (boundaryStubs family).decEq
  exact InducedPathComponentBoundarySchedule.next_ne_self_of_nodup_of_two_le
    (incidentStubs input) input.anchor (incidentStubs_nodup input)
    (anchor_mem_incidentStubs input) (two_le_incidentStubs_length input)

theorem successor_same_component (input : Input family) :
    component (successor input) = component input.anchor :=
  (mem_incidentStubs_iff input _).mp (successor_mem input)

noncomputable def DeclaredSuccessor (input : Input family)
    (anchor next : BoundaryStub family) : Prop :=
  anchor = input.anchor ∧ next = successor input

noncomputable def twoStubComponent (input : Input family) :
    TwoStubComponent family (DeclaredSuccessor input) where
  anchor := input.anchor
  successor := successor input
  distinct := successor_distinct input
  sameComponent := successor_same_component input
  declaredSuccessor := ⟨rfl, rfl⟩

noncomputable def componentObject (input : Input family) :
    FiniteObject (component input.anchor).supp where
  graph := (component input.anchor).toSimpleGraph
  input := {
    vertices := by
      let outside := outsideObject family
      letI : FinEnum (OutsideVertex family) := outside.input.vertices
      let accepted := Core.Enumeration.subtype outside.input.vertices
        (fun vertex => vertex ∈ componentVertices input)
        (fun _vertex => inferInstance)
      letI := accepted
      exact FinEnum.ofEquiv
        {vertex : OutsideVertex family // vertex ∈ componentVertices input}
        { toFun := fun vertex => ⟨vertex.1,
            (mem_componentVertices_iff input vertex.1).mpr vertex.2⟩
          invFun := fun vertex => ⟨vertex.1,
            (mem_componentVertices_iff input vertex.1).mp vertex.2⟩
          left_inv := by intro vertex; apply Subtype.ext; rfl
          right_inv := by intro vertex; apply Subtype.ext; rfl }
    decideAdj := by
      let outside := outsideObject family
      letI : DecidableRel outside.graph.Adj := outside.input.decideAdj
      exact fun left right => outside.input.decideAdj left.1 right.1
  }

noncomputable def bfsProfile (input : Input family) :
    OrderedBFSTree.Profile (componentObject input) where
  root := (twoStubComponent input).componentRoot

/-- Canonical declared-order BFS-tree shortest path in the same restricted
outside component. -/
noncomputable def componentPath (input : Input family) :=
  (bfsProfile input).treeWalk
    (twoStubComponent input).component_preconnected
    (twoStubComponent input).componentTarget

theorem componentPath_isPath (input : Input family) :
    (componentPath input).IsPath :=
  (bfsProfile input).treeWalk_isPath
    (twoStubComponent input).component_preconnected _

theorem componentPath_shortest (input : Input family) :
    (componentPath input).length =
      (component input.anchor).toSimpleGraph.dist
        (twoStubComponent input).componentRoot
        (twoStubComponent input).componentTarget :=
  (bfsProfile input).treeWalk_shortest
    (twoStubComponent input).component_preconnected _

/-- Full declared-order certificate for the selected return corridor.  The
path is shortest and its reverse parent word is lexicographically first in
the stored component-vertex order. -/
noncomputable def componentPathDeclaredOrderCertificate (input : Input family) :=
  (bfsProfile input).declaredOrderShortestPath
    (twoStubComponent input).component_preconnected
    (twoStubComponent input).componentTarget

@[simp]
theorem componentPathDeclaredOrderCertificate_path (input : Input family) :
    (componentPathDeclaredOrderCertificate input).path = componentPath input :=
  rfl

/-- The stored path support is bounded by the explicitly retained component
carrier. -/
theorem componentPath_support_length_le_component (input : Input family) :
    (componentPath input).support.length ≤
      (componentObject input).input.vertices.card := by
  letI : FinEnum (component input.anchor).supp :=
    (componentObject input).input.vertices
  simpa [FinEnum.card_eq_fintypeCard] using
    (componentPath_isPath input).support_nodup.length_le_card

end StructuralExhaustion.Graph.InducedPathRestrictedComponentBoundarySchedule
