import Erdos64EG.Future.P13WeightedColdRestrictedPriorPiecePair
import Erdos64EG.Future.P13WeightedColdRestrictedBoundedInterface
import Erdos64EG.Shared.CT15SparsePairResponses
import StructuralExhaustion.Core.FiniteCodeCollision
import StructuralExhaustion.Graph.FiniteActiveInterfaceD7Response
import StructuralExhaustion.Graph.FiniteActiveInterfaceD7Signature

namespace Erdos64EG.Internal

open StructuralExhaustion
open StructuralExhaustion.Graph

universe u

variable {ctx : Core.MinimalCounterexampleContext
  PackedProblem.{u} PackedTarget.{u}}
variable {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}

namespace P13WeightedColdRestrictedPrefixPackage

variable (package : P13WeightedColdRestrictedPrefixPackage ctx node21)

noncomputable abbrev D7Stage := sparsePairActivationStage ctx

noncomputable def d7AmbientVertex
    (vertex : (InducedPathRestrictedColdSkeleton.component
      package.input.anchor).supp) : ctx.G.Vertex :=
  vertex.1.1

noncomputable def d7PrefixAmbientSupport (stage : package.Stage) :
    Finset ctx.G.Vertex := by
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  exact (package.prefixSupport stage).map package.d7AmbientVertex |>.toFinset

noncomputable def d7DisplayedWindowSupport
    (window : InducedPathWindowLedger.WindowIndex ctx.G.object) :
    Finset ctx.G.Vertex := by
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  exact Finset.univ.image fun offset : Fin 13 =>
    InducedPathWindowLedger.selectedWindow ctx.G.object window offset

/-- Whole-prefix support observed by the current D7 projection, together with
both displayed windows.  It is finite but not uniformly bounded in `stage`. -/
noncomputable def d7ObservedSupport (stage : package.Stage) :
    Finset ctx.G.Vertex := by
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  exact package.d7PrefixAmbientSupport stage ∪
    d7DisplayedWindowSupport package.input.anchor.window ∪
    d7DisplayedWindowSupport
      (InducedPathRestrictedComponentBoundarySchedule.successor
        package.input).window

/-- D7 is filtered to the paper's two-window, two-endpoint carrier. -/
noncomputable def d7Interface (stage : package.Stage) :
    FiniteActiveInterfaceD7Response.Interface (ctx := ctx) where
  support := package.boundedActiveInterface stage
  bound := 30
  card_le := package.boundedActiveInterface_card_le_30 stage

/-! ## Carrier-local activated-slot recovery

The tuple order is endpoint, first shoulder, second shoulder.  Recovery scans
only the supplied endpoint's neighbor row to find the third neighbor (the
center), then the center's neighbor row to recover the canonical surplus-slot
index.  It validates all three port roles before retaining the slot. -/

abbrev D7CarrierVertex (stage : package.Stage) :=
  {vertex : ctx.G.Vertex // vertex ∈ package.boundedActiveInterface stage}

abbrev D7CarrierPortTuple (stage : package.Stage) :=
  package.D7CarrierVertex stage ×
    package.D7CarrierVertex stage × package.D7CarrierVertex stage

@[implicit_reducible] noncomputable def d7CarrierPortTuples
    (stage : package.Stage) : FinEnum (package.D7CarrierPortTuple stage) := by
  letI : FinEnum (package.D7CarrierVertex stage) :=
    package.boundedCarrierVertices stage
  infer_instance

noncomputable def recoverD7LocalSlot (stage : package.Stage)
    (tuple : package.D7CarrierPortTuple stage) : Option (ActiveSurplusSlot ctx) := by
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  let endpoint := tuple.1.1
  let first := tuple.2.1.1
  let second := tuple.2.2.1
  match (ctx.G.object.input.orderedNeighbors endpoint).values.find?
      (fun candidate => decide (candidate ≠ first ∧ candidate ≠ second)) with
  | none => exact none
  | some center =>
      match (ctx.G.object.input.orderedNeighbors center).values.findIdx?
          (fun candidate => decide (candidate = endpoint)) with
      | none => exact none
      | some index =>
          if bound : index < ctx.G.object.degree center - 3 then
            let slot : ActiveSurplusSlot ctx := ⟨center, ⟨index, bound⟩⟩
            if exactRoles :
                SurplusPortActivity.portEndpoint ctx.G.object slot = endpoint ∧
                SurplusPortActivity.firstShoulder ctx.G.object slot
                    (surplusPortActivationSetup ctx).deletionCritical = first ∧
                SurplusPortActivity.secondShoulder ctx.G.object slot
                    (surplusPortActivationSetup ctx).deletionCritical = second then
              exact some slot
            else exact none
          else exact none

theorem recoverD7LocalSlot_sound (stage : package.Stage)
    (tuple : package.D7CarrierPortTuple stage) (slot : ActiveSurplusSlot ctx)
    (recovered : package.recoverD7LocalSlot stage tuple = some slot) :
    SurplusPortActivity.portEndpoint ctx.G.object slot = tuple.1.1 ∧
      SurplusPortActivity.firstShoulder ctx.G.object slot
          (surplusPortActivationSetup ctx).deletionCritical = tuple.2.1.1 ∧
      SurplusPortActivity.secondShoulder ctx.G.object slot
          (surplusPortActivationSetup ctx).deletionCritical = tuple.2.2.1 := by
  unfold recoverD7LocalSlot at recovered
  dsimp only at recovered
  split at recovered <;> try contradiction
  split at recovered <;> try contradiction
  split at recovered <;> try contradiction
  split at recovered <;> try contradiction
  rename_i center centerResult index indexResult bound exactRoles
  simp only [Option.some.injEq] at recovered
  subst slot
  exact exactRoles

noncomputable def d7CarrierTupleOfSlot (stage : package.Stage)
    (slot : ActiveSurplusSlot ctx)
    (contained : SurplusPortActivation.PortSupport
      (surplusPortActivationSetup ctx) slot ⊆
        package.boundedActiveInterface stage) :
    package.D7CarrierPortTuple stage :=
  (⟨SurplusPortActivity.portEndpoint ctx.G.object slot,
      contained (SurplusPortActivation.portVertex_mem_portSupport
        (surplusPortActivationSetup ctx) slot .buffer)⟩,
    ⟨SurplusPortActivity.firstShoulder ctx.G.object slot
        (surplusPortActivationSetup ctx).deletionCritical,
      contained (SurplusPortActivation.portVertex_mem_portSupport
        (surplusPortActivationSetup ctx) slot .leftShoulder)⟩,
    ⟨SurplusPortActivity.secondShoulder ctx.G.object slot
        (surplusPortActivationSetup ctx).deletionCritical,
      contained (SurplusPortActivation.portVertex_mem_portSupport
        (surplusPortActivationSetup ctx) slot .rightShoulder)⟩)

set_option maxHeartbeats 800000 in
theorem recoverD7LocalSlot_of_slot (stage : package.Stage)
    (slot : ActiveSurplusSlot ctx)
    (contained : SurplusPortActivation.PortSupport
      (surplusPortActivationSetup ctx) slot ⊆
        package.boundedActiveInterface stage) :
    package.recoverD7LocalSlot stage
      (package.d7CarrierTupleOfSlot stage slot contained) = some slot := by
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  let object := ctx.G.object
  let center := slot.1
  let endpoint := SurplusPortActivity.portEndpoint object slot
  let first := SurplusPortActivity.firstShoulder object slot
    (surplusPortActivationSetup ctx).deletionCritical
  let second := SurplusPortActivity.secondShoulder object slot
    (surplusPortActivationSetup ctx).deletionCritical
  let endpointNeighbors := (object.input.orderedNeighbors endpoint).values
  have centerMember : center ∈ endpointNeighbors := by
    apply (object.input.mem_orderedNeighbors_iff endpoint center).2
    exact (SurplusPortActivity.portEndpoint_adjacent object slot).symm
  have centerNeFirst : center ≠ first := by
    exact (HighCenterPort.ne_center_of_mem_shoulders object center
      (SurplusPortActivity.portOfSlot object slot)
      (HighCenterPort.firstShoulder_mem object center
        (SurplusPortActivity.portCenter_high object slot)
        (surplusPortActivationSetup ctx).deletionCritical
        (SurplusPortActivity.portOfSlot object slot))).symm
  have centerNeSecond : center ≠ second := by
    exact (HighCenterPort.ne_center_of_mem_shoulders object center
      (SurplusPortActivity.portOfSlot object slot)
      (HighCenterPort.secondShoulder_mem object center
        (SurplusPortActivity.portCenter_high object slot)
        (surplusPortActivationSetup ctx).deletionCritical
        (SurplusPortActivity.portOfSlot object slot))).symm
  have onlyCenter : ∀ candidate ∈ endpointNeighbors,
      decide (candidate ≠ first ∧ candidate ≠ second) = true →
        candidate = center := by
    intro candidate member active
    by_contra neCenter
    have adjacent : object.graph.Adj endpoint candidate :=
      (object.input.mem_orderedNeighbors_iff endpoint candidate).1 member
    have shoulderMember :=
      HighCenterPort.mem_shoulders_of_adjacent_endpoint_of_ne_center
        object center (SurplusPortActivity.portOfSlot object slot)
        adjacent neCenter
    have cases := HighCenterPort.eq_firstShoulder_or_eq_secondShoulder_of_mem
      object center (SurplusPortActivity.portCenter_high object slot)
      (surplusPortActivationSetup ctx).deletionCritical
      (SurplusPortActivity.portOfSlot object slot) shoulderMember
    have activeProp : candidate ≠ first ∧ candidate ≠ second :=
      of_decide_eq_true active
    rcases cases with equalFirst | equalSecond
    · exact activeProp.1 equalFirst
    · exact activeProp.2 equalSecond
  have centerSearch : endpointNeighbors.find?
      (fun candidate => decide (candidate ≠ first ∧ candidate ≠ second)) =
        some center := by
    cases equation : endpointNeighbors.find?
        (fun candidate => decide (candidate ≠ first ∧ candidate ≠ second)) with
    | none =>
        have absent := (List.find?_eq_none.mp equation) center centerMember
        simp [centerNeFirst, centerNeSecond] at absent
    | some candidate =>
        have candidateActive := List.find?_some equation
        have candidateMember := List.mem_of_find?_eq_some equation
        have candidateExact := onlyCenter candidate candidateMember candidateActive
        subst candidate
        rfl
  have endpointAtIndex :
      (object.input.orderedNeighbors center).values[slot.2.1]'(by
        simpa [object] using SurplusPortActivity.portIndex_lt_neighbors object slot) =
        endpoint := by
    rfl
  have noEarlierEndpoint : ∀ index
      (indexBound : index < (object.input.orderedNeighbors center).values.length),
      index < slot.2.1 →
      ¬decide ((object.input.orderedNeighbors center).values[index]'indexBound =
        endpoint) = true := by
    intro index indexBound before equalBool
    have equalEndpoint := of_decide_eq_true equalBool
    have nodup := (object.input.orderedNeighbors center).nodup
    have earlierIndex :
        (object.input.orderedNeighbors center).values.idxOf endpoint = index := by
      rw [← equalEndpoint]
      exact List.get_idxOf nodup ⟨index, indexBound⟩
    have slotBound : slot.2.1 <
        (object.input.orderedNeighbors center).values.length := by
      simpa [object] using SurplusPortActivity.portIndex_lt_neighbors object slot
    have actualIndex :
        (object.input.orderedNeighbors center).values.idxOf endpoint = slot.2.1 := by
      have indexed := List.get_idxOf nodup
        ⟨slot.2.1, slotBound⟩
      simpa [endpointAtIndex] using indexed
    omega
  have indexSearch :
      (object.input.orderedNeighbors center).values.findIdx?
          (fun candidate => decide (candidate = endpoint)) = some slot.2.1 := by
    apply List.findIdx?_eq_some_iff_getElem.mpr
    let slotBound : slot.2.1 <
        (object.input.orderedNeighbors center).values.length := by
      simpa [object] using SurplusPortActivity.portIndex_lt_neighbors object slot
    refine ⟨slotBound, by simp [endpointAtIndex], ?_⟩
    intro index before
    exact noEarlierEndpoint index (before.trans slotBound) before
  unfold recoverD7LocalSlot
  simp only [d7CarrierTupleOfSlot]
  change (match endpointNeighbors.find?
      (fun candidate => decide (candidate ≠ first ∧ candidate ≠ second)) with
    | none => none
    | some recoveredCenter => _) = some slot
  rw [centerSearch]
  change (match (object.input.orderedNeighbors center).values.findIdx?
      (fun candidate => decide (candidate = endpoint)) with
    | none => none
    | some recoveredIndex => _) = some slot
  rw [indexSearch]
  simp [slot.2.isLt, center]

/-- The executable local slot list.  It evaluates `28^3` role tuples and
deduplicates recovered slots; it never enumerates the global surplus-slot
schedule. -/
noncomputable def d7LocalActivatedSlots (stage : package.Stage) :
    List (ActiveSurplusSlot ctx) := by
  classical
  exact ((package.d7CarrierPortTuples stage).orderedValues.filterMap
    (package.recoverD7LocalSlot stage)).dedup

theorem supportedD7Slot_mem_localActivatedSlots (stage : package.Stage)
    (slot : ActiveSurplusSlot ctx)
    (contained : SurplusPortActivation.PortSupport
      (surplusPortActivationSetup ctx) slot ⊆
        package.boundedActiveInterface stage) :
    slot ∈ package.d7LocalActivatedSlots stage := by
  classical
  unfold d7LocalActivatedSlots
  rw [List.mem_dedup, List.mem_filterMap]
  exact ⟨package.d7CarrierTupleOfSlot stage slot contained,
    (package.d7CarrierPortTuples stage).mem_orderedValues _,
    package.recoverD7LocalSlot_of_slot stage slot contained⟩

theorem d7LocalActivatedSlots_nodup (stage : package.Stage) :
    (package.d7LocalActivatedSlots stage).Nodup := by
  classical
  exact List.nodup_dedup _

theorem d7LocalActivatedSlots_length_le_28_cubed (stage : package.Stage) :
    (package.d7LocalActivatedSlots stage).length ≤ 28 ^ 3 := by
  classical
  calc
    (package.d7LocalActivatedSlots stage).length ≤
        (package.d7CarrierPortTuples stage).orderedValues.length := by
      unfold d7LocalActivatedSlots
      exact (List.dedup_sublist _).length_le.trans (List.length_filterMap_le _ _)
    _ = (package.d7CarrierPortTuples stage).card :=
      (package.d7CarrierPortTuples stage).orderedValues_length
    _ ≤ 28 ^ 3 := by
      letI : FinEnum (package.D7CarrierVertex stage) :=
        package.boundedCarrierVertices stage
      rw [FinEnum.card_eq_fintypeCard]
      simp only [Fintype.card_prod]
      have bound := package.boundedCarrierVertices_card_le_28 stage
      rw [FinEnum.card_eq_fintypeCard] at bound
      nlinarith

abbrev D7LocalActivatedSlot (stage : package.Stage) :=
  {slot : ActiveSurplusSlot ctx // slot ∈ package.d7LocalActivatedSlots stage}

@[implicit_reducible] noncomputable def d7LocalActivatedSlotEnumeration
    (stage : package.Stage) : FinEnum (package.D7LocalActivatedSlot stage) := by
  classical
  exact FinEnum.ofNodupList (package.d7LocalActivatedSlots stage).attach
    (by intro slot; exact List.mem_attach _ slot)
    ((package.d7LocalActivatedSlots_nodup stage).attach)

abbrev D7LocalActivatedSlotPair (stage : package.Stage) :=
  Core.Enumeration.OrderedDistinctPair
    (package.d7LocalActivatedSlotEnumeration stage)

@[implicit_reducible] noncomputable def d7LocalActivatedSlotPairs
    (stage : package.Stage) : FinEnum (package.D7LocalActivatedSlotPair stage) :=
  Core.Enumeration.orderedDistinctPairs
    (package.d7LocalActivatedSlotEnumeration stage)

/-- Reorient one locally generated pair by the manuscript's original global
slot order.  This compares two recovered slot indices; it does not enumerate
the global pair schedule. -/
noncomputable def d7LocalScheduledPair (stage : package.Stage)
    (pair : package.D7LocalActivatedSlotPair stage) :
    SurplusPairResponse.ScheduledPair
      (setup := surplusPortActivationSetup ctx) := by
  let first := Core.Enumeration.OrderedDistinctPair.first pair |>.1
  let second := Core.Enumeration.OrderedDistinctPair.second pair |>.1
  let slots := SurplusPairResponse.slotEnumeration
    (setup := surplusPortActivationSetup ctx)
  have distinct : first ≠ second := by
    intro equal
    apply Core.Enumeration.OrderedDistinctPair.distinct pair
    apply Subtype.ext
    exact equal
  by_cases ordered : (slots.equiv first).1 < (slots.equiv second).1
  · exact ⟨(first, second), ordered⟩
  · refine ⟨(second, first), ?_⟩
    have indexNe : (slots.equiv first).1 ≠ (slots.equiv second).1 := by
      intro equal
      apply distinct
      exact slots.equiv.injective (Fin.ext equal)
    exact lt_of_le_of_ne (Nat.le_of_not_gt ordered) indexNe.symm

noncomputable def d7LocalBlockerPair (stage : package.Stage)
    (pair : package.D7LocalActivatedSlotPair stage) :
    SurplusPairBlocker.Pair (setup := surplusPortActivationSetup ctx) :=
  (package.d7LocalScheduledPair stage pair).toBlockerPair

/-- A structurally clear locally recovered pair is the exact globally
oriented free-pair coordinate.  Only the two-slot orientation is imported
from the original schedule; no other global pair is scanned. -/
noncomputable def d7LocalClearFreePair (stage : package.Stage)
    (pair : package.D7LocalActivatedSlotPair stage)
    (clear : (package.d7LocalBlockerPair stage pair).StructuralClear
      (D7Stage (ctx := ctx))) :
    SurplusPairResponse.FreePair (D7Stage (ctx := ctx)) := by
  refine ⟨package.d7LocalScheduledPair stage pair, ?_⟩
  rintro ⟨candidate, member, blocks⟩
  exact clear.absent candidate member blocks

abbrev D7LocalPairExecution (stage : package.Stage) :=
  Sigma fun pair : package.D7LocalActivatedSlotPair stage =>
    (package.d7LocalBlockerPair stage pair).StructuralDecision
      (D7Stage (ctx := ctx))

/-- Run the existing pair-local blocker classifier only on pairs recovered
from carrier tuples. -/
noncomputable def d7LocalPairExecutions (stage : package.Stage) :
    List (package.D7LocalPairExecution stage) :=
  (package.d7LocalActivatedSlotPairs stage).orderedValues.map fun pair =>
    ⟨pair, (package.d7LocalBlockerPair stage pair).decideStructural
      (D7Stage (ctx := ctx))⟩

theorem d7LocalPairExecutions_length (stage : package.Stage) :
    (package.d7LocalPairExecutions stage).length =
      (package.d7LocalActivatedSlotPairs stage).card := by
  unfold d7LocalPairExecutions
  rw [List.length_map, FinEnum.orderedValues_length]

noncomputable def d7LocalSlotRawCoordinates (stage : package.Stage)
    (slot : package.D7LocalActivatedSlot stage) :
    List (FiniteActiveInterfaceD7Signature.RawCoordinate
      (D7Stage (ctx := ctx))) := by
  classical
  exact [.inl slot.1, .inr (.inl slot.1)] ++
    (if isOpen : FiniteActiveInterfaceD7Signature.IsOpen
        (D7Stage (ctx := ctx)) slot.1 then
      [.inr (.inr (.inl ⟨slot.1, isOpen⟩))]
    else []) ++
    (if isTriangular : FiniteActiveInterfaceD7Signature.IsTriangular
        (D7Stage (ctx := ctx)) slot.1 then
      [.inr (.inr (.inr (.inl ⟨slot.1, isTriangular⟩)))]
    else [])

noncomputable def d7LocalPairRawCoordinates (stage : package.Stage)
    (execution : package.D7LocalPairExecution stage) :
    List (FiniteActiveInterfaceD7Signature.RawCoordinate
      (D7Stage (ctx := ctx))) :=
  match execution with
  | ⟨_pair, .blocked _hit⟩ => []
  | ⟨pair, .pending clear⟩ =>
      [.inr (.inr (.inr (.inr
        (package.d7LocalClearFreePair stage pair clear))))]

/-- Complete candidate list generated from only locally recovered slots and
their locally classified pairs. -/
noncomputable def d7LocalRawCandidates (stage : package.Stage) :
    List (FiniteActiveInterfaceD7Signature.RawCoordinate
      (D7Stage (ctx := ctx))) :=
  (package.d7LocalActivatedSlotEnumeration stage).orderedValues.flatMap
      (package.d7LocalSlotRawCoordinates stage) ++
    (package.d7LocalPairExecutions stage).flatMap
      (package.d7LocalPairRawCoordinates stage)

noncomputable def d7LocalDeclaredCoordinates (stage : package.Stage) :
    List (FiniteActiveInterfaceD7Signature.Coordinate
      (D7Stage (ctx := ctx)) (package.d7Interface stage)) := by
  classical
  exact ((package.d7LocalRawCandidates stage).filterMap fun coordinate =>
    if contained : FiniteActiveInterfaceD7Signature.support
        (D7Stage (ctx := ctx)) coordinate ⊆
        package.boundedActiveInterface stage then
      some ⟨coordinate, contained⟩
    else none).dedup

theorem d7LocalDeclaredCoordinates_nodup (stage : package.Stage) :
    (package.d7LocalDeclaredCoordinates stage).Nodup := by
  classical
  exact List.nodup_dedup _

theorem d7LocalDeclaredCoordinates_support (stage : package.Stage)
    (coordinate : FiniteActiveInterfaceD7Signature.Coordinate
      (D7Stage (ctx := ctx)) (package.d7Interface stage))
    (member : coordinate ∈ package.d7LocalDeclaredCoordinates stage) :
    FiniteActiveInterfaceD7Signature.support
        (D7Stage (ctx := ctx)) coordinate.1 ⊆
      package.boundedActiveInterface stage :=
  coordinate.2

theorem d7LocalRawCandidate_mem_declared (stage : package.Stage)
    (coordinate : FiniteActiveInterfaceD7Signature.RawCoordinate
      (D7Stage (ctx := ctx)))
    (contained : FiniteActiveInterfaceD7Signature.support
      (D7Stage (ctx := ctx)) coordinate ⊆
        package.boundedActiveInterface stage)
    (member : coordinate ∈ package.d7LocalRawCandidates stage) :
    (⟨coordinate, contained⟩ : FiniteActiveInterfaceD7Signature.Coordinate
      (D7Stage (ctx := ctx)) (package.d7Interface stage)) ∈
        package.d7LocalDeclaredCoordinates stage := by
  classical
  unfold d7LocalDeclaredCoordinates
  rw [List.mem_dedup, List.mem_filterMap]
  exact ⟨coordinate, member, by simp [contained]⟩

theorem d7LocalSlotRawCoordinates_complete (stage : package.Stage)
    (slot : ActiveSurplusSlot ctx)
    (slotMember : slot ∈ package.d7LocalActivatedSlots stage) :
    let localSlot : package.D7LocalActivatedSlot stage := ⟨slot, slotMember⟩
    (.inl slot : FiniteActiveInterfaceD7Signature.RawCoordinate
        (D7Stage (ctx := ctx))) ∈
          package.d7LocalSlotRawCoordinates stage localSlot ∧
      (.inr (.inl slot) : FiniteActiveInterfaceD7Signature.RawCoordinate
        (D7Stage (ctx := ctx))) ∈
          package.d7LocalSlotRawCoordinates stage localSlot := by
  dsimp
  simp [d7LocalSlotRawCoordinates]

theorem d7LocalSlotRawCandidates_complete (stage : package.Stage)
    (slot : ActiveSurplusSlot ctx)
    (slotMember : slot ∈ package.d7LocalActivatedSlots stage) :
    (.inl slot : FiniteActiveInterfaceD7Signature.RawCoordinate
        (D7Stage (ctx := ctx))) ∈ package.d7LocalRawCandidates stage ∧
      (.inr (.inl slot) : FiniteActiveInterfaceD7Signature.RawCoordinate
        (D7Stage (ctx := ctx))) ∈ package.d7LocalRawCandidates stage := by
  let localSlot : package.D7LocalActivatedSlot stage := ⟨slot, slotMember⟩
  have localSlotMember : localSlot ∈
      (package.d7LocalActivatedSlotEnumeration stage).orderedValues :=
    (package.d7LocalActivatedSlotEnumeration stage).mem_orderedValues localSlot
  have localCompleteness :=
    package.d7LocalSlotRawCoordinates_complete stage slot slotMember
  constructor
  · apply List.mem_append_left
    exact List.mem_flatMap_of_mem localSlotMember localCompleteness.1
  · apply List.mem_append_left
    exact List.mem_flatMap_of_mem localSlotMember localCompleteness.2

theorem d7LocalOpenRawCandidate_complete (stage : package.Stage)
    (slot : FiniteActiveInterfaceD7Signature.OpenSlot
      (D7Stage (ctx := ctx)))
    (slotMember : slot.1 ∈ package.d7LocalActivatedSlots stage) :
    (.inr (.inr (.inl slot)) :
      FiniteActiveInterfaceD7Signature.RawCoordinate
        (D7Stage (ctx := ctx))) ∈ package.d7LocalRawCandidates stage := by
  let localSlot : package.D7LocalActivatedSlot stage := ⟨slot.1, slotMember⟩
  have localSlotMember : localSlot ∈
      (package.d7LocalActivatedSlotEnumeration stage).orderedValues :=
    (package.d7LocalActivatedSlotEnumeration stage).mem_orderedValues localSlot
  apply List.mem_append_left
  apply List.mem_flatMap_of_mem localSlotMember
  simp [d7LocalSlotRawCoordinates, localSlot, slot.2]

theorem d7LocalTriangularRawCandidate_complete (stage : package.Stage)
    (slot : FiniteActiveInterfaceD7Signature.TriangularSlot
      (D7Stage (ctx := ctx)))
    (slotMember : slot.1 ∈ package.d7LocalActivatedSlots stage) :
    (.inr (.inr (.inr (.inl slot))) :
      FiniteActiveInterfaceD7Signature.RawCoordinate
        (D7Stage (ctx := ctx))) ∈ package.d7LocalRawCandidates stage := by
  let localSlot : package.D7LocalActivatedSlot stage := ⟨slot.1, slotMember⟩
  have localSlotMember : localSlot ∈
      (package.d7LocalActivatedSlotEnumeration stage).orderedValues :=
    (package.d7LocalActivatedSlotEnumeration stage).mem_orderedValues localSlot
  apply List.mem_append_left
  apply List.mem_flatMap_of_mem localSlotMember
  simp [d7LocalSlotRawCoordinates, localSlot, slot.2]

theorem d7LocalScheduledPair_exists (stage : package.Stage)
    (scheduled : SurplusPairResponse.ScheduledPair
      (setup := surplusPortActivationSetup ctx))
    (firstMember : scheduled.first ∈ package.d7LocalActivatedSlots stage)
    (secondMember : scheduled.second ∈ package.d7LocalActivatedSlots stage) :
    ∃ localPair : package.D7LocalActivatedSlotPair stage,
      package.d7LocalScheduledPair stage localPair = scheduled := by
  let localEnumeration := package.d7LocalActivatedSlotEnumeration stage
  let firstLocal : package.D7LocalActivatedSlot stage :=
    ⟨scheduled.first, firstMember⟩
  let secondLocal : package.D7LocalActivatedSlot stage :=
    ⟨scheduled.second, secondMember⟩
  have localDistinct : firstLocal ≠ secondLocal := by
    intro equal
    exact scheduled.distinct (congrArg Subtype.val equal)
  by_cases localOrdered :
      (localEnumeration.equiv firstLocal).1 <
        (localEnumeration.equiv secondLocal).1
  · let localPair : package.D7LocalActivatedSlotPair stage :=
      ⟨(firstLocal, secondLocal), localOrdered⟩
    refine ⟨localPair, ?_⟩
    apply Subtype.ext
    simp [d7LocalScheduledPair, localPair, firstLocal, secondLocal,
      localEnumeration, Core.Enumeration.OrderedDistinctPair.first,
      Core.Enumeration.OrderedDistinctPair.second,
      SurplusPairResponse.ScheduledPair.first,
      SurplusPairResponse.ScheduledPair.second, scheduled.2]
  · have localIndexNe : (localEnumeration.equiv firstLocal).1 ≠
        (localEnumeration.equiv secondLocal).1 := by
      intro equal
      exact localDistinct (localEnumeration.equiv.injective (Fin.ext equal))
    have reverseOrdered : (localEnumeration.equiv secondLocal).1 <
        (localEnumeration.equiv firstLocal).1 :=
      lt_of_le_of_ne (Nat.le_of_not_gt localOrdered) localIndexNe.symm
    let localPair : package.D7LocalActivatedSlotPair stage :=
      ⟨(secondLocal, firstLocal), reverseOrdered⟩
    refine ⟨localPair, ?_⟩
    have notReverseRaw : ¬
        ((SurplusPairResponse.slotEnumeration
          (setup := surplusPortActivationSetup ctx)).equiv scheduled.1.2).1 <
        ((SurplusPairResponse.slotEnumeration
          (setup := surplusPortActivationSetup ctx)).equiv scheduled.1.1).1 :=
      Nat.not_lt_of_ge (Nat.le_of_lt scheduled.2)
    apply Subtype.ext
    simp [d7LocalScheduledPair, localPair, firstLocal, secondLocal,
      localEnumeration, Core.Enumeration.OrderedDistinctPair.first,
      Core.Enumeration.OrderedDistinctPair.second,
      SurplusPairResponse.ScheduledPair.first,
      SurplusPairResponse.ScheduledPair.second, scheduled.2, notReverseRaw]

theorem d7LocalFreePairRawCandidate_complete (stage : package.Stage)
    (pair : SurplusPairResponse.FreePair (D7Stage (ctx := ctx)))
    (firstMember : pair.1.first ∈ package.d7LocalActivatedSlots stage)
    (secondMember : pair.1.second ∈ package.d7LocalActivatedSlots stage) :
    (.inr (.inr (.inr (.inr pair))) :
      FiniteActiveInterfaceD7Signature.RawCoordinate
        (D7Stage (ctx := ctx))) ∈ package.d7LocalRawCandidates stage := by
  classical
  obtain ⟨localPair, scheduledExact⟩ :=
    package.d7LocalScheduledPair_exists stage pair.1 firstMember secondMember
  have blockerExact : package.d7LocalBlockerPair stage localPair =
      pair.1.toBlockerPair := congrArg SurplusPairResponse.ScheduledPair.toBlockerPair
        scheduledExact
  generalize decisionEq :
      (package.d7LocalBlockerPair stage localPair).decideStructural
        (D7Stage (ctx := ctx)) = decision
  cases decision with
  | blocked hit =>
      exfalso
      apply pair.2
      refine ⟨hit.value, ?_, ?_⟩
      · simpa [SurplusPairResponse.blockerFamily,
          SurplusPairResponse.localBlockerProfile, blockerExact] using hit.member
      · simpa [SurplusPairResponse.blockerFamily,
          SurplusPairResponse.localBlockerProfile, blockerExact] using hit.holds
  | pending clear =>
      let execution : package.D7LocalPairExecution stage :=
        ⟨localPair, .pending clear⟩
      have executionMember : execution ∈ package.d7LocalPairExecutions stage := by
        have pairMember :=
          (package.d7LocalActivatedSlotPairs stage).mem_orderedValues localPair
        have mapped : (⟨localPair,
              (package.d7LocalBlockerPair stage localPair).decideStructural
                (D7Stage (ctx := ctx))⟩ :
              package.D7LocalPairExecution stage) ∈
            package.d7LocalPairExecutions stage := by
          exact List.mem_map_of_mem pairMember
        have executionExact : (⟨localPair,
              (package.d7LocalBlockerPair stage localPair).decideStructural
                (D7Stage (ctx := ctx))⟩ :
              package.D7LocalPairExecution stage) = execution := by
          simp [execution, decisionEq]
        exact executionExact ▸ mapped
      apply List.mem_append_right
      have freePairExact : package.d7LocalClearFreePair stage localPair clear = pair := by
        apply Subtype.ext
        exact scheduledExact
      exact List.mem_flatMap_of_mem executionMember (by
        simp [d7LocalPairRawCoordinates, execution, freePairExact])

/-- The carrier-local schedule is complete for the manuscript's globally
declared D7 family after the single complete-support restriction.  The proof
recovers slot coordinates from their three-vertex port support and recovers a
free pair from the two `Gamma` supports already contained in its connector
support.  No ambient slot, pair, coordinate, or Boolean universe is scanned. -/
theorem every_supported_declared_d7_coordinate_is_local (stage : package.Stage)
    (coordinate : FiniteActiveInterfaceD7Signature.RawCoordinate
      (D7Stage (ctx := ctx)))
    (contained : FiniteActiveInterfaceD7Signature.support
      (D7Stage (ctx := ctx)) coordinate ⊆
        package.boundedActiveInterface stage) :
    (⟨coordinate, contained⟩ : FiniteActiveInterfaceD7Signature.Coordinate
      (D7Stage (ctx := ctx)) (package.d7Interface stage)) ∈
        package.d7LocalDeclaredCoordinates stage := by
  cases coordinate with
  | inl slot =>
      have slotMember := package.supportedD7Slot_mem_localActivatedSlots
        stage slot (by
          simpa [FiniteActiveInterfaceD7Signature.support] using contained)
      exact package.d7LocalRawCandidate_mem_declared stage _ contained
        (package.d7LocalSlotRawCandidates_complete stage slot slotMember).1
  | inr rest =>
      cases rest with
      | inl slot =>
          have portContained : SurplusPortActivation.PortSupport
              (surplusPortActivationSetup ctx) slot ⊆
              package.boundedActiveInterface stage := by
            intro vertex member
            apply contained
            simp [FiniteActiveInterfaceD7Signature.support, member]
          have slotMember := package.supportedD7Slot_mem_localActivatedSlots
            stage slot portContained
          exact package.d7LocalRawCandidate_mem_declared stage _ contained
            (package.d7LocalSlotRawCandidates_complete stage slot slotMember).2
      | inr rest =>
          cases rest with
          | inl slot =>
              have portContained : SurplusPortActivation.PortSupport
                  (surplusPortActivationSetup ctx) slot.1 ⊆
                  package.boundedActiveInterface stage := by
                intro vertex member
                apply contained
                simp [FiniteActiveInterfaceD7Signature.support, member]
              have slotMember := package.supportedD7Slot_mem_localActivatedSlots
                stage slot.1 portContained
              exact package.d7LocalRawCandidate_mem_declared stage _ contained
                (package.d7LocalOpenRawCandidate_complete stage slot slotMember)
          | inr rest =>
              cases rest with
              | inl slot =>
                  have portContained : SurplusPortActivation.PortSupport
                      (surplusPortActivationSetup ctx) slot.1 ⊆
                      package.boundedActiveInterface stage := by
                    intro vertex member
                    apply contained
                    simp [FiniteActiveInterfaceD7Signature.support, member]
                  have slotMember :=
                    package.supportedD7Slot_mem_localActivatedSlots
                      stage slot.1 portContained
                  exact package.d7LocalRawCandidate_mem_declared stage _ contained
                    (package.d7LocalTriangularRawCandidate_complete
                      stage slot slotMember)
              | inr pair =>
                  have firstPortContained : SurplusPortActivation.PortSupport
                      (surplusPortActivationSetup ctx) pair.1.first ⊆
                      package.boundedActiveInterface stage := by
                    intro vertex member
                    apply contained
                    exact pair.firstGamma_subset_support (D7Stage (ctx := ctx))
                      ((D7Stage (ctx := ctx)).demand pair.1.first
                        |>.portSupport_subset_GammaVertices member)
                  have secondPortContained : SurplusPortActivation.PortSupport
                      (surplusPortActivationSetup ctx) pair.1.second ⊆
                      package.boundedActiveInterface stage := by
                    intro vertex member
                    apply contained
                    exact pair.secondGamma_subset_support (D7Stage (ctx := ctx))
                      ((D7Stage (ctx := ctx)).demand pair.1.second
                        |>.portSupport_subset_GammaVertices member)
                  have firstMember :=
                    package.supportedD7Slot_mem_localActivatedSlots
                      stage pair.1.first firstPortContained
                  have secondMember :=
                    package.supportedD7Slot_mem_localActivatedSlots
                      stage pair.1.second secondPortContained
                  exact package.d7LocalRawCandidate_mem_declared stage _ contained
                    (package.d7LocalFreePairRawCandidate_complete stage pair
                      firstMember secondMember)

abbrev D7Coordinate (stage : package.Stage) :=
  (package.d7Interface stage).Coordinate (D7Stage (ctx := ctx))

@[implicit_reducible]
noncomputable def d7Coordinates (stage : package.Stage) :
    FinEnum (package.D7Coordinate stage) :=
  (package.d7Interface stage).coordinates (D7Stage (ctx := ctx))

theorem d7Coordinate_support_subset_interface (stage : package.Stage)
    (coordinate : package.D7Coordinate stage) :
    coordinate.1.support (D7Stage (ctx := ctx)) ⊆
      package.boundedActiveInterface stage :=
  coordinate.2

/-- Exact context-indexed D7 value on one declared sparse-surplus coordinate. -/
noncomputable def d7Response (stage : package.Stage)
    (coordinate : package.D7Coordinate stage)
    (outside : PackedBoundariedGluing.Context ctx.G.Vertex) : Bool :=
  (FiniteActiveInterfaceD7Response.Interface.responseProfile
    (D7Stage (ctx := ctx)) (package.d7Interface stage)).responseSystem.response
      coordinate outside

theorem d7Response_true_iff (stage : package.Stage)
    (coordinate : package.D7Coordinate stage)
    (outside : PackedBoundariedGluing.Context ctx.G.Vertex) :
    package.d7Response stage coordinate outside = true ↔
      packedStaticInput.Target
        (PackedBoundariedGluing.glue ctx.G.object.input.vertices
          (((package.d7Interface stage).responseProfile
            (D7Stage (ctx := ctx))).coordinatePiece coordinate)
          outside) :=
  by
    exact (package.d7Interface stage).response_true_iff
      (D7Stage (ctx := ctx)) coordinate outside

abbrev D7ContextCode (stage : package.Stage) :=
  (package.d7Interface stage).ContextCode (D7Stage (ctx := ctx))

/-- Projection of one supplied outside context to the exact D7 vector.  This
does not enumerate the Boolean cube or any outside-context family. -/
noncomputable def d7RestrictContext (stage : package.Stage)
    (outside : PackedBoundariedGluing.Context ctx.G.Vertex) :
    package.D7ContextCode stage :=
  (package.d7Interface stage).restrictContext (D7Stage (ctx := ctx)) outside

theorem d7RestrictContext_apply (stage : package.Stage)
    (outside : PackedBoundariedGluing.Context ctx.G.Vertex)
    (coordinate : package.D7Coordinate stage) :
    package.d7RestrictContext stage outside coordinate =
      package.d7Response stage coordinate outside := by
  rfl

theorem d7ContextEncoding (stage : package.Stage)
    (outside : PackedBoundariedGluing.Context ctx.G.Vertex) :
    ∃ code : package.D7ContextCode stage,
      code = package.d7RestrictContext stage outside :=
  (package.d7Interface stage).contextEncoding
    (D7Stage (ctx := ctx)) outside

theorem d7CoordinateCount_le_sparsePairs (stage : package.Stage) :
    (package.d7Coordinates stage).card ≤
      (SurplusPairResponse.freePairEnumeration
        (D7Stage (ctx := ctx))).card :=
  (package.d7Interface stage).coordinates_card_le_freePairs
    (D7Stage (ctx := ctx))

/-! The complete clause-(D7) signature.  The earlier declarations above are
the sparse-pair summand retained for compatibility with its existing response
profile.  These declarations add, without identifying labels, the selected
port, root-return, open-suppression, triangle, triangular-return, and pair
families required by the manuscript. -/

abbrev D7DeclaredRawCoordinate :=
  FiniteActiveInterfaceD7Signature.RawCoordinate (D7Stage (ctx := ctx))

abbrev D7DeclaredCoordinate (stage : package.Stage) :=
  FiniteActiveInterfaceD7Signature.Coordinate
    (D7Stage (ctx := ctx)) (package.d7Interface stage)

@[implicit_reducible]
noncomputable def d7DeclaredCoordinates (stage : package.Stage) :
    FinEnum (package.D7DeclaredCoordinate stage) := by
  classical
  apply FinEnum.ofNodupList (package.d7LocalDeclaredCoordinates stage)
  · intro coordinate
    exact package.every_supported_declared_d7_coordinate_is_local
      stage coordinate.1 coordinate.2
  · exact package.d7LocalDeclaredCoordinates_nodup stage

theorem d7DeclaredCoordinate_support_subset_interface (stage : package.Stage)
    (coordinate : package.D7DeclaredCoordinate stage) :
    FiniteActiveInterfaceD7Signature.support
      (D7Stage (ctx := ctx)) coordinate.1 ⊆
      package.boundedActiveInterface stage :=
  FiniteActiveInterfaceD7Signature.coordinate_support_subset
    (D7Stage (ctx := ctx)) (package.d7Interface stage) coordinate

noncomputable def d7DeclaredExactValue
    (coordinate : D7DeclaredRawCoordinate (ctx := ctx))
    (outside : PackedBoundariedGluing.Context ctx.G.Vertex) :=
  FiniteActiveInterfaceD7Signature.exactValue
    (D7Stage (ctx := ctx)) coordinate outside

theorem every_supported_declared_d7_coordinate_is_stored (stage : package.Stage)
    (coordinate : D7DeclaredRawCoordinate (ctx := ctx))
    (contained : FiniteActiveInterfaceD7Signature.support
      (D7Stage (ctx := ctx)) coordinate ⊆
      package.boundedActiveInterface stage) :
    ∃ proof, (⟨coordinate, proof⟩ : package.D7DeclaredCoordinate stage) ∈
      (package.d7DeclaredCoordinates stage).orderedValues :=
  ⟨contained, (package.d7DeclaredCoordinates stage).mem_orderedValues _⟩

noncomputable def d7DeclaredChecks : Nat :=
  FiniteActiveInterfaceD7Signature.checks (D7Stage (ctx := ctx))

theorem d7DeclaredCoordinateCount_le_checks (stage : package.Stage) :
    (package.d7DeclaredCoordinates stage).card ≤
      d7DeclaredChecks (ctx := ctx) := by
  calc
    (package.d7DeclaredCoordinates stage).card =
        (FiniteActiveInterfaceD7Signature.coordinates
          (D7Stage (ctx := ctx)) (package.d7Interface stage)).card :=
      FinEnum.card_unique _ _
    _ ≤ d7DeclaredChecks (ctx := ctx) :=
      FiniteActiveInterfaceD7Signature.coordinates_card_le_checks
        (D7Stage (ctx := ctx)) (package.d7Interface stage)

/-! ## Fixed support-role normalization

This normalization deliberately does not identify the activated slot stored
inside a coordinate.  The port support has three vertices but does not store
the high center/activation row, so recovering slot identity requires a local
producer ledger rather than an ambient slot scan. -/

inductive D7FamilyTag
  | selectedPort
  | rootReturn
  | openSuppression
  | triangularResponse
  | sparsePairResponse
  deriving DecidableEq, Repr, Fintype

def d7FamilyTag : D7DeclaredRawCoordinate (ctx := ctx) → D7FamilyTag
  | .inl _ => .selectedPort
  | .inr (.inl _) => .rootReturn
  | .inr (.inr (.inl _)) => .openSuppression
  | .inr (.inr (.inr (.inl _))) => .triangularResponse
  | .inr (.inr (.inr (.inr _))) => .sparsePairResponse

abbrev D7StructuralSupportCode :=
  D7FamilyTag × (BoundedCarrierRole → Bool)

theorem d7StructuralSupportCode_card :
    Fintype.card D7StructuralSupportCode = 5 * 2 ^ 28 := by
  change Fintype.card (D7FamilyTag ×
    ((Fin 13 ⊕ (Fin 13 ⊕ Bool)) → Bool)) = 5 * 2 ^ 28
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_sum,
    Fintype.card_fin, Fintype.card_bool]
  rw [show Fintype.card D7FamilyTag = 5 by native_decide]

noncomputable def d7DeclaredSupportRoleMask (stage : package.Stage)
    (coordinate : D7DeclaredRawCoordinate (ctx := ctx)) :
    BoundedCarrierRole → Bool := by
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  exact fun role => decide
    (package.boundedCarrierRoleVertex stage role ∈
      FiniteActiveInterfaceD7Signature.support
        (D7Stage (ctx := ctx)) coordinate)

noncomputable def d7StructuralSupportCode (stage : package.Stage)
    (coordinate : package.D7DeclaredCoordinate stage) :
    D7StructuralSupportCode :=
  (d7FamilyTag coordinate.1,
    package.d7DeclaredSupportRoleMask stage coordinate.1)

theorem d7StructuralSupportCode_eq_implies_support_eq
    (stage : package.Stage)
    (left right : package.D7DeclaredCoordinate stage)
    (equal : package.d7StructuralSupportCode stage left =
      package.d7StructuralSupportCode stage right) :
    d7FamilyTag left.1 = d7FamilyTag right.1 ∧
      FiniteActiveInterfaceD7Signature.support
          (D7Stage (ctx := ctx)) left.1 =
        FiniteActiveInterfaceD7Signature.support
          (D7Stage (ctx := ctx)) right.1 := by
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  constructor
  · exact congrArg Prod.fst equal
  · have masksEqual : package.d7DeclaredSupportRoleMask stage left.1 =
        package.d7DeclaredSupportRoleMask stage right.1 :=
      congrArg Prod.snd equal
    apply Finset.ext
    intro vertex
    constructor
    · intro leftMember
      have carrierMember : vertex ∈ package.boundedActiveInterface stage :=
        left.2 leftMember
      obtain ⟨role, roleExact⟩ :=
        (package.mem_boundedActiveInterface_iff_role stage vertex).mp carrierMember
      have bitEqual := congrFun masksEqual role
      have leftTrue : package.d7DeclaredSupportRoleMask stage left.1 role = true := by
        simp [d7DeclaredSupportRoleMask, roleExact, leftMember]
      have rightTrue : package.d7DeclaredSupportRoleMask stage right.1 role = true := by
        rw [← bitEqual]
        exact leftTrue
      have rightRoleMember : package.boundedCarrierRoleVertex stage role ∈
          FiniteActiveInterfaceD7Signature.support
            (D7Stage (ctx := ctx)) right.1 := by
        apply of_decide_eq_true
        exact rightTrue
      simpa [roleExact] using rightRoleMember
    · intro rightMember
      have carrierMember : vertex ∈ package.boundedActiveInterface stage :=
        right.2 rightMember
      obtain ⟨role, roleExact⟩ :=
        (package.mem_boundedActiveInterface_iff_role stage vertex).mp carrierMember
      have bitEqual := congrFun masksEqual role
      have rightTrue : package.d7DeclaredSupportRoleMask stage right.1 role = true := by
        simp [d7DeclaredSupportRoleMask, roleExact, rightMember]
      have leftTrue : package.d7DeclaredSupportRoleMask stage left.1 role = true := by
        rw [bitEqual]
        exact rightTrue
      have leftRoleMember : package.boundedCarrierRoleVertex stage role ∈
          FiniteActiveInterfaceD7Signature.support
            (D7Stage (ctx := ctx)) left.1 := by
        apply of_decide_eq_true
        exact leftTrue
      simpa [roleExact] using leftRoleMember

/-! ## Exact carrier-role labels

The support mask above is useful for accounting, but it is not the declared
coordinate label: two different activated slots can have the same family and
the same unlabelled support.  The manuscript keeps those labels distinct.
The exact local label of a slot is its ordered `(endpoint, first shoulder,
second shoulder)` tuple, with every vertex replaced by its first semantic
carrier role.  A sparse-pair label is the ordered pair of its two slot labels.
The resulting alphabet is fixed and symbolic; it is never enumerated. -/

abbrev D7SlotRoleCode :=
  BoundedCarrierRole × BoundedCarrierRole × BoundedCarrierRole

/-- Four singleton-slot families followed by the ordered sparse-pair family. -/
abbrev D7FullLabelCode :=
  D7SlotRoleCode ⊕
    (D7SlotRoleCode ⊕
      (D7SlotRoleCode ⊕
        (D7SlotRoleCode ⊕ (D7SlotRoleCode × D7SlotRoleCode))))

theorem d7SlotRoleCode_card : Fintype.card D7SlotRoleCode = 28 ^ 3 := by
  change Fintype.card
    ((Fin 13 ⊕ (Fin 13 ⊕ Bool)) ×
      (Fin 13 ⊕ (Fin 13 ⊕ Bool)) ×
      (Fin 13 ⊕ (Fin 13 ⊕ Bool))) = 28 ^ 3
  simp only [Fintype.card_prod, Fintype.card_sum, Fintype.card_fin,
    Fintype.card_bool]
  norm_num

def d7FullLabelCodeBound : Nat := 4 * 28 ^ 3 + (28 ^ 3) ^ 2

noncomputable def d7SlotRoleCode (stage : package.Stage)
    (slot : ActiveSurplusSlot ctx)
    (contained : SurplusPortActivation.PortSupport
      (surplusPortActivationSetup ctx) slot ⊆
        package.boundedActiveInterface stage) : D7SlotRoleCode :=
  let endpoint := SurplusPortActivity.portEndpoint ctx.G.object slot
  let first := SurplusPortActivity.firstShoulder ctx.G.object slot
    (surplusPortActivationSetup ctx).deletionCritical
  let second := SurplusPortActivity.secondShoulder ctx.G.object slot
    (surplusPortActivationSetup ctx).deletionCritical
  ((package.boundedCarrierCode stage endpoint
      (contained (SurplusPortActivation.portVertex_mem_portSupport
        (surplusPortActivationSetup ctx) slot .buffer))).role,
    (package.boundedCarrierCode stage first
      (contained (SurplusPortActivation.portVertex_mem_portSupport
        (surplusPortActivationSetup ctx) slot .leftShoulder))).role,
    (package.boundedCarrierCode stage second
      (contained (SurplusPortActivation.portVertex_mem_portSupport
        (surplusPortActivationSetup ctx) slot .rightShoulder))).role)

theorem d7SlotRoleCode_injective (stage : package.Stage)
    (left right : ActiveSurplusSlot ctx)
    (leftContained : SurplusPortActivation.PortSupport
      (surplusPortActivationSetup ctx) left ⊆
        package.boundedActiveInterface stage)
    (rightContained : SurplusPortActivation.PortSupport
      (surplusPortActivationSetup ctx) right ⊆
        package.boundedActiveInterface stage)
    (equal : package.d7SlotRoleCode stage left leftContained =
      package.d7SlotRoleCode stage right rightContained) : left = right := by
  let leftTuple := package.d7CarrierTupleOfSlot stage left leftContained
  let rightTuple := package.d7CarrierTupleOfSlot stage right rightContained
  have endpointRole :
      (package.d7SlotRoleCode stage left leftContained).1 =
        (package.d7SlotRoleCode stage right rightContained).1 :=
    congrArg Prod.fst equal
  have firstRole :
      (package.d7SlotRoleCode stage left leftContained).2.1 =
        (package.d7SlotRoleCode stage right rightContained).2.1 :=
    congrArg (fun code => code.2.1) equal
  have secondRole :
      (package.d7SlotRoleCode stage left leftContained).2.2 =
        (package.d7SlotRoleCode stage right rightContained).2.2 :=
    congrArg (fun code => code.2.2) equal
  have endpointEqual : leftTuple.1.1 = rightTuple.1.1 := by
    change SurplusPortActivity.portEndpoint ctx.G.object left =
      SurplusPortActivity.portEndpoint ctx.G.object right
    exact package.boundedCarrierCode_injective stage _ _ (by
      simpa [d7SlotRoleCode] using endpointRole)
  have firstEqual : leftTuple.2.1.1 = rightTuple.2.1.1 := by
    change SurplusPortActivity.firstShoulder ctx.G.object left
        (surplusPortActivationSetup ctx).deletionCritical =
      SurplusPortActivity.firstShoulder ctx.G.object right
        (surplusPortActivationSetup ctx).deletionCritical
    exact package.boundedCarrierCode_injective stage _ _ (by
      simpa [d7SlotRoleCode] using firstRole)
  have secondEqual : leftTuple.2.2.1 = rightTuple.2.2.1 := by
    change SurplusPortActivity.secondShoulder ctx.G.object left
        (surplusPortActivationSetup ctx).deletionCritical =
      SurplusPortActivity.secondShoulder ctx.G.object right
        (surplusPortActivationSetup ctx).deletionCritical
    exact package.boundedCarrierCode_injective stage _ _ (by
      simpa [d7SlotRoleCode] using secondRole)
  have tupleEqual : leftTuple = rightTuple := by
    apply Prod.ext
    · exact Subtype.ext endpointEqual
    · apply Prod.ext
      · exact Subtype.ext firstEqual
      · exact Subtype.ext secondEqual
  have leftRecovered := package.recoverD7LocalSlot_of_slot
    stage left leftContained
  have rightRecovered := package.recoverD7LocalSlot_of_slot
    stage right rightContained
  change package.recoverD7LocalSlot stage leftTuple = some left at leftRecovered
  change package.recoverD7LocalSlot stage rightTuple = some right at rightRecovered
  rw [tupleEqual, rightRecovered] at leftRecovered
  exact (Option.some.inj leftRecovered).symm

private theorem selectedPortContained (stage : package.Stage)
    (slot : ActiveSurplusSlot ctx)
    (contained : FiniteActiveInterfaceD7Signature.SupportContained
      (D7Stage (ctx := ctx)) (package.d7Interface stage) (.inl slot)) :
    SurplusPortActivation.PortSupport (surplusPortActivationSetup ctx) slot ⊆
      package.boundedActiveInterface stage := by
  change FiniteActiveInterfaceD7Signature.support
      (D7Stage (ctx := ctx)) (.inl slot) ⊆
        package.boundedActiveInterface stage at contained
  simpa [FiniteActiveInterfaceD7Signature.support] using contained

private theorem rootReturnPortContained (stage : package.Stage)
    (slot : ActiveSurplusSlot ctx)
    (contained : FiniteActiveInterfaceD7Signature.SupportContained
      (D7Stage (ctx := ctx)) (package.d7Interface stage) (.inr (.inl slot))) :
    SurplusPortActivation.PortSupport (surplusPortActivationSetup ctx) slot ⊆
      package.boundedActiveInterface stage := by
  intro vertex member
  apply contained
  simp [FiniteActiveInterfaceD7Signature.support, member]

private theorem openPortContained (stage : package.Stage)
    (slot : FiniteActiveInterfaceD7Signature.OpenSlot (D7Stage (ctx := ctx)))
    (contained : FiniteActiveInterfaceD7Signature.SupportContained
      (D7Stage (ctx := ctx)) (package.d7Interface stage)
        (.inr (.inr (.inl slot)))) :
    SurplusPortActivation.PortSupport (surplusPortActivationSetup ctx) slot.1 ⊆
      package.boundedActiveInterface stage := by
  intro vertex member
  apply contained
  simp [FiniteActiveInterfaceD7Signature.support, member]

private theorem triangularPortContained (stage : package.Stage)
    (slot : FiniteActiveInterfaceD7Signature.TriangularSlot
      (D7Stage (ctx := ctx)))
    (contained : FiniteActiveInterfaceD7Signature.SupportContained
      (D7Stage (ctx := ctx)) (package.d7Interface stage)
        (.inr (.inr (.inr (.inl slot))))) :
    SurplusPortActivation.PortSupport (surplusPortActivationSetup ctx) slot.1 ⊆
      package.boundedActiveInterface stage := by
  intro vertex member
  apply contained
  simp [FiniteActiveInterfaceD7Signature.support, member]

private theorem pairFirstPortContained (stage : package.Stage)
    (pair : SurplusPairResponse.FreePair (D7Stage (ctx := ctx)))
    (contained : FiniteActiveInterfaceD7Signature.SupportContained
      (D7Stage (ctx := ctx)) (package.d7Interface stage)
        (.inr (.inr (.inr (.inr pair))))) :
    SurplusPortActivation.PortSupport (surplusPortActivationSetup ctx)
        pair.1.first ⊆ package.boundedActiveInterface stage := by
  intro vertex member
  apply contained
  exact pair.firstGamma_subset_support (D7Stage (ctx := ctx))
    ((D7Stage (ctx := ctx)).demand pair.1.first
      |>.portSupport_subset_GammaVertices member)

private theorem pairSecondPortContained (stage : package.Stage)
    (pair : SurplusPairResponse.FreePair (D7Stage (ctx := ctx)))
    (contained : FiniteActiveInterfaceD7Signature.SupportContained
      (D7Stage (ctx := ctx)) (package.d7Interface stage)
        (.inr (.inr (.inr (.inr pair))))) :
    SurplusPortActivation.PortSupport (surplusPortActivationSetup ctx)
        pair.1.second ⊆ package.boundedActiveInterface stage := by
  intro vertex member
  apply contained
  exact pair.secondGamma_subset_support (D7Stage (ctx := ctx))
    ((D7Stage (ctx := ctx)).demand pair.1.second
      |>.portSupport_subset_GammaVertices member)

/-- Complete paper label, with no quotienting by coincident values. -/
noncomputable def d7FullLabelCode (stage : package.Stage) :
    package.D7DeclaredCoordinate stage → D7FullLabelCode := by
  intro coordinate
  rcases coordinate with ⟨raw, contained⟩
  rcases raw with slot | rest
  · exact .inl (package.d7SlotRoleCode stage slot
      (selectedPortContained package stage slot contained))
  · rcases rest with slot | rest
    · exact .inr (.inl (package.d7SlotRoleCode stage slot
        (rootReturnPortContained package stage slot contained)))
    · rcases rest with slot | rest
      · exact .inr (.inr (.inl (package.d7SlotRoleCode stage slot.1
          (openPortContained package stage slot contained))))
      · rcases rest with slot | pair
        · exact .inr (.inr (.inr (.inl
            (package.d7SlotRoleCode stage slot.1
              (triangularPortContained package stage slot contained)))))
        · exact .inr (.inr (.inr (.inr
            (package.d7SlotRoleCode stage pair.1.first
                (pairFirstPortContained package stage pair contained),
              package.d7SlotRoleCode stage pair.1.second
                (pairSecondPortContained package stage pair contained)))))

/-- The fixed role code is the complete D7 label: equality of codes forces
equality of the original labelled coordinates, independently of their values
in any outside context. -/
theorem d7FullLabelCode_injective (stage : package.Stage) :
    Function.Injective (package.d7FullLabelCode stage) := by
  intro left right equal
  rcases left with ⟨leftRaw, leftContained⟩
  rcases right with ⟨rightRaw, rightContained⟩
  rcases leftRaw with leftSlot | leftRest
  · rcases rightRaw with rightSlot | rightRest
    · have codeEqual : package.d7SlotRoleCode stage leftSlot
          (selectedPortContained package stage leftSlot leftContained) =
        package.d7SlotRoleCode stage rightSlot
          (selectedPortContained package stage rightSlot rightContained) := by
        simpa [d7FullLabelCode] using equal
      have slotEqual := package.d7SlotRoleCode_injective stage leftSlot rightSlot
        (selectedPortContained package stage leftSlot leftContained)
        (selectedPortContained package stage rightSlot rightContained) codeEqual
      subst rightSlot
      rfl
    · rcases rightRest with _ | _ | _ | _ <;>
        simp [d7FullLabelCode] at equal
  · rcases leftRest with leftSlot | leftRest
    · rcases rightRaw with rightSlot | rightRest
      · simp [d7FullLabelCode] at equal
      · rcases rightRest with rightSlot | rightRest
        · have codeEqual : package.d7SlotRoleCode stage leftSlot
              (rootReturnPortContained package stage leftSlot leftContained) =
            package.d7SlotRoleCode stage rightSlot
              (rootReturnPortContained package stage rightSlot rightContained) := by
            simpa [d7FullLabelCode] using equal
          have slotEqual := package.d7SlotRoleCode_injective stage leftSlot rightSlot
            (rootReturnPortContained package stage leftSlot leftContained)
            (rootReturnPortContained package stage rightSlot rightContained) codeEqual
          subst rightSlot
          rfl
        · rcases rightRest with _ | _ | _ <;>
            simp [d7FullLabelCode] at equal
    · rcases leftRest with leftSlot | leftRest
      · rcases rightRaw with rightSlot | rightRest
        · simp [d7FullLabelCode] at equal
        · rcases rightRest with rightSlot | rightRest
          · simp [d7FullLabelCode] at equal
          · rcases rightRest with rightSlot | rightRest
            · have codeEqual : package.d7SlotRoleCode stage leftSlot.1
                  (openPortContained package stage leftSlot leftContained) =
                package.d7SlotRoleCode stage rightSlot.1
                  (openPortContained package stage rightSlot rightContained) := by
                simpa [d7FullLabelCode] using equal
              have slotEqual := package.d7SlotRoleCode_injective stage
                leftSlot.1 rightSlot.1
                (openPortContained package stage leftSlot leftContained)
                (openPortContained package stage rightSlot rightContained) codeEqual
              have labelledSlotEqual : leftSlot = rightSlot := Subtype.ext slotEqual
              subst rightSlot
              rfl
            · rcases rightRest with _ | _ <;>
                simp [d7FullLabelCode] at equal
      · rcases leftRest with leftSlot | leftPair
        · rcases rightRaw with rightSlot | rightRest
          · simp [d7FullLabelCode] at equal
          · rcases rightRest with rightSlot | rightRest
            · simp [d7FullLabelCode] at equal
            · rcases rightRest with rightSlot | rightRest
              · simp [d7FullLabelCode] at equal
              · rcases rightRest with rightSlot | rightPair
                · have codeEqual : package.d7SlotRoleCode stage leftSlot.1
                      (triangularPortContained package stage leftSlot leftContained) =
                    package.d7SlotRoleCode stage rightSlot.1
                      (triangularPortContained package stage rightSlot rightContained) := by
                    simpa [d7FullLabelCode] using equal
                  have slotEqual := package.d7SlotRoleCode_injective stage
                    leftSlot.1 rightSlot.1
                    (triangularPortContained package stage leftSlot leftContained)
                    (triangularPortContained package stage rightSlot rightContained)
                    codeEqual
                  have labelledSlotEqual : leftSlot = rightSlot := Subtype.ext slotEqual
                  subst rightSlot
                  rfl
                · simp [d7FullLabelCode] at equal
        · rcases rightRaw with rightSlot | rightRest
          · simp [d7FullLabelCode] at equal
          · rcases rightRest with rightSlot | rightRest
            · simp [d7FullLabelCode] at equal
            · rcases rightRest with rightSlot | rightRest
              · simp [d7FullLabelCode] at equal
              · rcases rightRest with rightSlot | rightPair
                · simp [d7FullLabelCode] at equal
                · have firstCodeEqual : package.d7SlotRoleCode stage
                        leftPair.1.first
                        (pairFirstPortContained package stage leftPair leftContained) =
                      package.d7SlotRoleCode stage rightPair.1.first
                        (pairFirstPortContained package stage rightPair rightContained) := by
                      simp only [d7FullLabelCode] at equal
                      exact congrArg Prod.fst (Sum.inr.inj
                        (Sum.inr.inj (Sum.inr.inj (Sum.inr.inj equal))))
                  have secondCodeEqual : package.d7SlotRoleCode stage
                        leftPair.1.second
                        (pairSecondPortContained package stage leftPair leftContained) =
                      package.d7SlotRoleCode stage rightPair.1.second
                        (pairSecondPortContained package stage rightPair rightContained) := by
                      simp only [d7FullLabelCode] at equal
                      exact congrArg Prod.snd (Sum.inr.inj
                        (Sum.inr.inj (Sum.inr.inj (Sum.inr.inj equal))))
                  have firstEqual := package.d7SlotRoleCode_injective stage
                      leftPair.1.first rightPair.1.first
                      (pairFirstPortContained package stage leftPair leftContained)
                      (pairFirstPortContained package stage rightPair rightContained)
                      firstCodeEqual
                  have secondEqual := package.d7SlotRoleCode_injective stage
                      leftPair.1.second rightPair.1.second
                      (pairSecondPortContained package stage leftPair leftContained)
                      (pairSecondPortContained package stage rightPair rightContained)
                      secondCodeEqual
                  have scheduledEqual : leftPair.1 = rightPair.1 := by
                    apply Subtype.ext
                    exact Prod.ext firstEqual secondEqual
                  have pairEqual : leftPair = rightPair := Subtype.ext scheduledEqual
                  subst rightPair
                  rfl

/-! ## Complete embedded D7 values

The moving endpoint prevents comparing ambient vertices literally across two
prefixes.  We therefore normalize every proof-selected walk to its ordered
sequence of semantic carrier roles.  Every such walk is a path whose complete
support lies in the 28-occurrence carrier, so its sequence has length at most
28.  The dependent finite-vector type is used only as a symbolic codomain; no
vector alphabet is materialized. -/

abbrev FixedD7RoleList :=
  Sigma fun length : Fin 29 => Fin length.1 → BoundedCarrierRole

noncomputable instance : Fintype FixedD7RoleList := by
  letI : (length : Fin 29) →
      Fintype (Fin length.1 → BoundedCarrierRole) := fun _ => inferInstance
  infer_instance

noncomputable def d7RoleOfVertex (stage : package.Stage)
    (vertex : ctx.G.Vertex)
    (member : vertex ∈ package.boundedActiveInterface stage) :
    BoundedCarrierRole :=
  (package.boundedCarrierCode stage vertex member).role

private theorem d7SupportedPathLength_le_28 (stage : package.Stage)
    (vertices : List ctx.G.Vertex) (nodup : vertices.Nodup)
    (supported : ∀ vertex ∈ vertices,
      vertex ∈ package.boundedActiveInterface stage) :
    vertices.length ≤ 28 := by
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  calc
    vertices.length = vertices.toFinset.card :=
      (List.toFinset_card_of_nodup nodup).symm
    _ ≤ (package.boundedActiveInterface stage).card :=
      Finset.card_le_card (by
        intro vertex member
        exact supported vertex (by simpa using member))
    _ ≤ 28 := package.boundedActiveInterface_card_le_28 stage

noncomputable def d7FixedRoleList (stage : package.Stage)
    (vertices : List ctx.G.Vertex)
    (supported : ∀ vertex ∈ vertices,
      vertex ∈ package.boundedActiveInterface stage)
    (bound : vertices.length ≤ 28) : FixedD7RoleList :=
  ⟨⟨vertices.length, Nat.lt_succ_iff.mpr bound⟩,
    fun index => package.d7RoleOfVertex stage
      (vertices.get ⟨index.1, by simpa using index.2⟩)
      (supported _ (List.get_mem vertices _))⟩

/-- The five embedded value families.  Sparse-pair target response is omitted
here on purpose: it is the context-dependent Boolean compared by F2. -/
abbrev FixedD7EmbeddedValue :=
  Unit ⊕ (FixedD7RoleList ⊕
    (FixedD7RoleList ⊕ (FixedD7RoleList ⊕ FixedD7RoleList)))

noncomputable instance : Fintype FixedD7EmbeddedValue := by infer_instance

noncomputable def d7FixedEmbeddedValue (stage : package.Stage) :
    package.D7DeclaredCoordinate stage → FixedD7EmbeddedValue := by
  intro coordinate
  rcases coordinate with ⟨raw, contained⟩
  rcases raw with slot | rest
  · exact .inl ()
  · rcases rest with slot | rest
    · let path := (SurplusPortActivation.rootReturn
          (surplusPortActivationSetup ctx) slot).path
      have supported : ∀ vertex ∈ path.support,
          vertex ∈ package.boundedActiveInterface stage := by
        intro vertex member
        apply contained
        simp [FiniteActiveInterfaceD7Signature.support, path, member]
      have bound := d7SupportedPathLength_le_28 (package := package)
        stage path.support
          (SurplusPortActivation.rootReturn
            (surplusPortActivationSetup ctx) slot).isPath.support_nodup supported
      exact .inr (.inl (package.d7FixedRoleList stage path.support supported bound))
    · rcases rest with slot | rest
      · let response := FiniteActiveInterfaceD7Signature.openResponse
            (D7Stage (ctx := ctx)) slot
        let path := response.path
        have supported : ∀ vertex ∈ path.support,
            vertex ∈ package.boundedActiveInterface stage := by
          intro vertex member
          apply contained
          simp [FiniteActiveInterfaceD7Signature.support, response, path, member]
        have bound := d7SupportedPathLength_le_28 (package := package)
          stage path.support response.pathIsSimple.support_nodup supported
        exact .inr (.inr (.inl
          (package.d7FixedRoleList stage path.support supported bound)))
      · rcases rest with slot | pair
        · let path := SurplusPortActivation.triangle
              (surplusPortActivationSetup ctx) slot.1
              (FiniteActiveInterfaceD7Signature.triangularIsTriangular
                (D7Stage (ctx := ctx)) slot)
          have supported : ∀ vertex ∈ path.support,
              vertex ∈ package.boundedActiveInterface stage := by
            intro vertex member
            apply contained
            simp [FiniteActiveInterfaceD7Signature.support, path, member]
          have pathLength : path.length = 3 := by
            simpa [path] using SurplusPortActivation.triangle_length
              (surplusPortActivationSetup ctx) slot.1
                (FiniteActiveInterfaceD7Signature.triangularIsTriangular
                  (D7Stage (ctx := ctx)) slot)
          have supportLength : path.support.length = path.length + 1 :=
            path.length_support
          have bound : path.support.length ≤ 28 := by omega
          exact .inr (.inr (.inr (.inl
            (package.d7FixedRoleList stage path.support supported bound))))
        · let connector := pair.connector (D7Stage (ctx := ctx))
          let path := connector.path
          have supported : ∀ vertex ∈ path.support,
              vertex ∈ package.boundedActiveInterface stage := by
            intro vertex member
            apply contained
            exact connector.path_subset_support vertex member
          have bound := d7SupportedPathLength_le_28 (package := package)
            stage path.support connector.isPath.support_nodup supported
          exact .inr (.inr (.inr (.inr
            (package.d7FixedRoleList stage path.support supported bound))))

/-- Complete cross-prefix D7 datum prior to the F2 outside-context test. -/
structure FixedD7Code where
  label : D7FullLabelCode
  support : BoundedCarrierRole → Bool
  embedded : FixedD7EmbeddedValue

noncomputable instance : DecidableEq FixedD7Code := Classical.decEq _
noncomputable instance : Fintype FixedD7Code := by
  classical
  letI : Fintype D7FullLabelCode := inferInstance
  letI : Fintype (BoundedCarrierRole → Bool) := inferInstance
  letI : Fintype FixedD7EmbeddedValue := inferInstance
  exact Fintype.ofEquiv
    (D7FullLabelCode × (BoundedCarrierRole → Bool) × FixedD7EmbeddedValue)
    {
      toFun := fun ⟨label, support, embedded⟩ => ⟨label, support, embedded⟩
      invFun := fun code => (code.label, code.support, code.embedded)
      left_inv := by intro code; cases code; rfl
      right_inv := by intro code; cases code; rfl
    }

noncomputable def fixedD7Code (stage : package.Stage)
    (coordinate : package.D7DeclaredCoordinate stage) : FixedD7Code where
  label := package.d7FullLabelCode stage coordinate
  support := package.d7DeclaredSupportRoleMask stage coordinate.1
  embedded := package.d7FixedEmbeddedValue stage coordinate

theorem fixedD7Code_injective (stage : package.Stage) :
    Function.Injective (package.fixedD7Code stage) := by
  intro left right equal
  exact package.d7FullLabelCode_injective stage
    (congrArg FixedD7Code.label equal)

/-- Cross-stage equality exposes the complete role-normalized local datum.
It does not assert equality of the context-dependent target response. -/
theorem fixedD7Code_eq_components {stage prior : package.Stage}
    (current : package.D7DeclaredCoordinate stage)
    (earlier : package.D7DeclaredCoordinate prior)
    (equal : package.fixedD7Code stage current =
      package.fixedD7Code prior earlier) :
    package.d7FullLabelCode stage current =
        package.d7FullLabelCode prior earlier ∧
      package.d7DeclaredSupportRoleMask stage current.1 =
        package.d7DeclaredSupportRoleMask prior earlier.1 ∧
      package.d7FixedEmbeddedValue stage current =
        package.d7FixedEmbeddedValue prior earlier := by
  exact ⟨congrArg FixedD7Code.label equal,
    congrArg FixedD7Code.support equal,
    congrArg FixedD7Code.embedded equal⟩

/-- A concrete same-code collision, retaining the two distinct exact D7
coordinates.  The family equality and complete support equality are derived,
not assumed separately. -/
structure D7EqualSupportCodePair (stage : package.Stage) where
  left : package.D7DeclaredCoordinate stage
  right : package.D7DeclaredCoordinate stage
  distinct : left ≠ right
  codeEqual : package.d7StructuralSupportCode stage left =
    package.d7StructuralSupportCode stage right

namespace D7EqualSupportCodePair

variable {package} {stage : package.Stage}

theorem familyEqual (pair : package.D7EqualSupportCodePair stage) :
    d7FamilyTag pair.left.1 = d7FamilyTag pair.right.1 :=
  (package.d7StructuralSupportCode_eq_implies_support_eq stage
    pair.left pair.right pair.codeEqual).1

theorem supportEqual (pair : package.D7EqualSupportCodePair stage) :
    FiniteActiveInterfaceD7Signature.support
        (D7Stage (ctx := ctx)) pair.left.1 =
      FiniteActiveInterfaceD7Signature.support
        (D7Stage (ctx := ctx)) pair.right.1 :=
  (package.d7StructuralSupportCode_eq_implies_support_eq stage
    pair.left pair.right pair.codeEqual).2

end D7EqualSupportCodePair

inductive D7LocalCodeDecision (stage : package.Stage)
  | collision (pair : package.D7EqualSupportCodePair stage)
  | unique (codesNodup :
      ((package.d7LocalDeclaredCoordinates stage).map
        (package.d7StructuralSupportCode stage)).Nodup)

/-- First same-code collision over only the locally generated D7 list.  The
fixed `5 * 2^28` code universe is never enumerated. -/
noncomputable def runD7LocalCodeDecision (stage : package.Stage) :
    package.D7LocalCodeDecision stage := by
  let code := package.d7StructuralSupportCode stage
  let items := package.d7LocalDeclaredCoordinates stage
  cases result : Core.FiniteCodeCollision.decideWithDecEq code items with
  | unique codesNodup => exact .unique codesNodup
  | collision collision =>
      exact .collision {
        left := collision.first
        right := collision.second
        distinct := collision.first_ne_second_of_nodup
          (package.d7LocalDeclaredCoordinates_nodup stage)
        codeEqual := collision.code_eq }

theorem runD7LocalCodeDecision_total (stage : package.Stage) :
    (∃ pair, package.runD7LocalCodeDecision stage = .collision pair) ∨
      (∃ codesNodup,
        package.runD7LocalCodeDecision stage = .unique codesNodup) := by
  cases equation : package.runD7LocalCodeDecision stage with
  | collision pair => exact .inl ⟨pair, rfl⟩
  | unique codesNodup => exact .inr ⟨codesNodup, rfl⟩

noncomputable def fixedD7Codes (stage : package.Stage) : List FixedD7Code :=
  (package.d7LocalDeclaredCoordinates stage).map
    (package.fixedD7Code stage)

theorem fixedD7Codes_nodup (stage : package.Stage) :
    (package.fixedD7Codes stage).Nodup := by
  unfold fixedD7Codes
  exact (package.d7LocalDeclaredCoordinates_nodup stage).map
    (package.fixedD7Code_injective stage)

noncomputable def fixedD7CodeSet (stage : package.Stage) :
    Finset FixedD7Code := by
  classical
  exact (package.fixedD7Codes stage).toFinset

theorem mem_fixedD7CodeSet_iff (stage : package.Stage) (code : FixedD7Code) :
    code ∈ package.fixedD7CodeSet stage ↔
      ∃ coordinate : package.D7DeclaredCoordinate stage,
        package.fixedD7Code stage coordinate = code := by
  classical
  change code ∈ (package.fixedD7Codes stage).toFinset ↔ _
  rw [List.mem_toFinset]
  constructor
  · intro member
    rcases List.mem_map.mp member with ⟨coordinate, _, codeExact⟩
    exact ⟨coordinate, codeExact⟩
  · rintro ⟨coordinate, rfl⟩
    apply List.mem_map.mpr
    exact ⟨coordinate,
      package.every_supported_declared_d7_coordinate_is_local
        stage coordinate.1 coordinate.2, rfl⟩

theorem fixedD7Codes_length_le_alphabet (stage : package.Stage) :
    (package.fixedD7Codes stage).length ≤ Fintype.card FixedD7Code :=
  (package.fixedD7Codes_nodup stage).length_le_card

/-- Executable equality of the two observed D7 slices.  The scan compares
only the actual fixed code sets; it never enumerates `FixedD7Code`. -/
inductive D7FixedStateComparison (stage prior : package.Stage) where
  | same (equal : package.fixedD7CodeSet stage =
      package.fixedD7CodeSet prior)
  | different (notEqual : package.fixedD7CodeSet stage ≠
      package.fixedD7CodeSet prior)

noncomputable def compareFixedD7States (stage prior : package.Stage) :
    package.D7FixedStateComparison stage prior := by
  classical
  by_cases equal : package.fixedD7CodeSet stage = package.fixedD7CodeSet prior
  · exact .same equal
  · exact .different equal

theorem compareFixedD7States_total (stage prior : package.Stage) :
    (∃ equal, package.compareFixedD7States stage prior = .same equal) ∨
      (∃ notEqual,
        package.compareFixedD7States stage prior = .different notEqual) := by
  cases equation : package.compareFixedD7States stage prior with
  | same equal => exact .inl ⟨equal, rfl⟩
  | different notEqual => exact .inr ⟨notEqual, rfl⟩

theorem d7DeclaredChecks_polynomial :
    d7DeclaredChecks (ctx := ctx) ≤
      4 * ctx.G.object.input.vertices.card ^ 2 +
        ctx.G.object.input.vertices.card ^ 4 :=
  FiniteActiveInterfaceD7Signature.checks_le_polynomial
    (D7Stage (ctx := ctx))

namespace PriorPiecePair

variable {package : P13WeightedColdRestrictedPrefixPackage ctx node21}
variable {stage prior : package.Stage}
variable (pair : package.PriorPiecePair stage prior)

theorem earlier_support_subset_current :
    pair.earlier.support ⊆ pair.current.support := by
  letI : DecidableEq
      (InducedPathRestrictedColdSkeleton.component
        package.input.anchor).supp :=
    (InducedPathRestrictedComponentBoundarySchedule.componentObject
      package.input).input.vertices.decEq
  rw [pair.earlier_eq, pair.current_eq]
  intro vertex member
  rw [FiniteTwoBoundaryPiece.ofWalkPrefix_support,
    FiniteTwoBoundaryPiece.prefixFinset, List.mem_toFinset] at member ⊢
  exact package.prefixSupport_subset
    (Nat.le_of_lt (package.priorStage_val_lt stage prior pair.prior_mem)) member

end PriorPiecePair

end P13WeightedColdRestrictedPrefixPackage

end Erdos64EG.Internal
