import Erdos64EG.Future.P13ProducedPriorSupportLedger
import Erdos64EG.Future.P13WeightedColdRestrictedBoundedInterface
import Erdos64EG.Future.P13WeightedColdRestrictedPrefixStages
import StructuralExhaustion.Core.FiniteActiveSupportProjection
import StructuralExhaustion.Core.ResidualRefinement
import StructuralExhaustion.Core.FiniteRoleSupportNormalization
import StructuralExhaustion.Graph.ResidualSupportRefinement
import StructuralExhaustion.Graph.TypeBDecoratedArmCoordinate

namespace Erdos64EG.Internal

open StructuralExhaustion
open StructuralExhaustion.Graph
open StructuralExhaustion.Graph.InducedPathWindowLedger

universe u

/-!
# Clause D6 on a restricted cold-prefix interface

Node `[153]` may inspect only Type-B and route-8 supports that an earlier
branch has actually produced.  This module projects that append-only ledger to
the finite support observed at one literal cold-prefix stage.  A current endpoint in a recorded support
is the exact F4 handoff.  If no recorded support contains it, the negative
result retains the complete finite D6 projection for the cut state.

The later Type-B certificate-label, fan-window, hybrid-incidence, candidate,
and overlap data are not imported backwards: the current prior-event value
does not contain them.  The decorated event stored here nevertheless retains
its center, fan-safe first-neighbour pairs, source core, boundary-degree and
arm-terminal responses, and all proof-carrying arms.
-/

variable {ctx : Core.MinimalCounterexampleContext
  PackedProblem.{u} PackedTarget.{u}}
variable {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}

namespace P13WeightedColdRestrictedPrefixPackage

variable (package : P13WeightedColdRestrictedPrefixPackage ctx node21)

abbrev PriorD6Event
    (_package : P13WeightedColdRestrictedPrefixPackage ctx node21) :=
  P13ProducedPriorSupportLedger.Event (ctx := ctx)

/-- Producer provenance accumulated at every literal occurrence.  Each case
contains the exact proof-carrying output of an existing manuscript producer. -/
inductive PriorD6Origin :
    P13ProducedPriorSupportLedger.Event (ctx := ctx) → Prop
  | ordinary (entry : P13ProducedPriorSupportLedger.Node64To65Ordinary
      (ctx := ctx)) : PriorD6Origin (.first entry)
  | decorated (entry : TypeBProducedSupportLedgerConnector.RecordedDecoratedHandoff
      (ctx := ctx)) : PriorD6Origin (.second entry)
  | routeEight (entry : P13ProducedPriorSupportLedger.RecordedRouteEightExtraction
      (ctx := ctx)) : PriorD6Origin (.third entry)

abbrev AccumulatedPriorD6Ledger :=
  Core.ResidualRefinement.Ledger.{u, u + 3}
    (P13ProducedPriorSupportLedger.Event (ctx := ctx))
    [PriorD6Origin]

/-- The only graph-specific datum needed by the reusable accumulated-support
runner. -/
noncomputable def priorD6SupportProfile :
    Graph.ResidualSupportRefinement.Profile
      (Event := P13ProducedPriorSupportLedger.Event (ctx := ctx))
      ctx.G.Vertex where
  vertexDecEq := ctx.G.object.input.vertices.decEq
  support := P13ProducedPriorSupportLedger.eventSupport

/-- Exact F4 branch state built only from the three existing proof-carrying
producer ledgers: the ordinary `[64] -> [65]` edge, the decorated `[108] ->
`[66] -> [65]` edge, and route 8. -/
structure ProducedPriorD6State where
  baseState : AccumulatedPriorD6Ledger (ctx := ctx)

/-- The only D6 predecessor carrier is the complete accumulated residual.
Every downstream projection remains indexed by its literal occurrences. -/
abbrev PriorD6Ledger
    (_package : P13WeightedColdRestrictedPrefixPackage ctx node21) :=
  ProducedPriorD6State (ctx := ctx)

noncomputable def ProducedPriorD6State.base
    (state : ProducedPriorD6State (ctx := ctx)) :=
  state.baseState.residuals

noncomputable def producedPriorD6State
    (baseState : AccumulatedPriorD6Ledger (ctx := ctx)) :
    ProducedPriorD6State (ctx := ctx) where
  baseState := baseState

theorem ProducedPriorD6State.event_origin
    (state : ProducedPriorD6State (ctx := ctx))
    (occurrence : state.baseState.residuals.Occurrence) :
    PriorD6Origin (state.baseState.residuals.event occurrence) :=
  state.baseState.require
    (property := PriorD6Origin)
    occurrence

/-- Ambient vertex underlying a vertex of the selected restricted component. -/
abbrev ambientVertex
    (vertex : (InducedPathRestrictedColdSkeleton.component
      package.input.anchor).supp) : ctx.G.Vertex :=
  vertex.1.1

/-- The ambient projection forgets two nested subtype proofs and is therefore
injective.  Keeping this theorem beside the transparent projection prevents
later dependent consumers from unfolding the entire cold package. -/
theorem ambientVertex_injective : Function.Injective package.ambientVertex :=
  Subtype.val_injective.comp Subtype.val_injective

/-- Literal ambient vertices read by the current stored corridor prefix. -/
noncomputable def prefixAmbientSupport (stage : package.Stage) :
    Finset ctx.G.Vertex := by
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  exact (package.prefixSupport stage).map package.ambientVertex |>.toFinset

/-- The current graph-derived endpoint, not an arbitrary queried vertex. -/
noncomputable def currentAmbientEndpoint (stage : package.Stage) : ctx.G.Vertex :=
  package.ambientVertex
    ((InducedPathRestrictedComponentBoundarySchedule.componentPath
      package.input).getVert stage.val)

/-- Distinct ordered positions of the canonical simple component path have
distinct actual ambient endpoints.  This graph fact lives beside the endpoint
projection so downstream germ code does not reopen the dependent package. -/
theorem currentAmbientEndpoint_ne_of_val_lt
    (earlier later : package.Stage) (ordered : earlier.val < later.val) :
    package.currentAmbientEndpoint earlier ≠
      package.currentAmbientEndpoint later := by
  intro equal
  have pathVerticesEqual :
      (InducedPathRestrictedComponentBoundarySchedule.componentPath
        package.input).getVert earlier.val =
      (InducedPathRestrictedComponentBoundarySchedule.componentPath
        package.input).getVert later.val :=
    package.ambientVertex_injective equal
  have earlierLe : earlier.val ≤
      (InducedPathRestrictedComponentBoundarySchedule.componentPath
        package.input).length := by
    have earlierBound := earlier.isLt
    have supportLength :=
      (InducedPathRestrictedComponentBoundarySchedule.componentPath
        package.input).length_support
    omega
  have laterLe : later.val ≤
      (InducedPathRestrictedComponentBoundarySchedule.componentPath
        package.input).length := by
    have laterBound := later.isLt
    have supportLength :=
      (InducedPathRestrictedComponentBoundarySchedule.componentPath
        package.input).length_support
    omega
  have indicesEqual :=
    (InducedPathRestrictedComponentBoundarySchedule.componentPath_isPath
      package.input).getVert_injOn earlierLe laterLe pathVerticesEqual
  exact (Nat.ne_of_lt ordered) indicesEqual

/-- Authoritative occurrence-indexed F4 support view. -/
noncomputable def ProducedPriorD6State.supportView
    (state : ProducedPriorD6State (ctx := ctx)) :=
  (priorD6SupportProfile (ctx := ctx)).view state.baseState

/-- Exact F4 scan on persistent occurrences.  A hit retains the production
occurrence even when another occurrence emits an equal event value. -/
noncomputable def ProducedPriorD6State.recognizeF4
    (state : ProducedPriorD6State (ctx := ctx)) (stage : package.Stage) :=
  (priorD6SupportProfile (ctx := ctx)).recognize state.baseState
    (package.currentAmbientEndpoint stage)

theorem ProducedPriorD6State.recognizeF4_exact
    (state : ProducedPriorD6State (ctx := ctx)) (stage : package.Stage) :
    match state.recognizeF4 package stage with
    | .found hit =>
        hit.occurrence ∈ state.base.entries ∧
          package.currentAmbientEndpoint stage ∈
            P13ProducedPriorSupportLedger.eventSupport
              hit.state.residual ∧
          PriorD6Origin hit.state.residual
    | .absent _ =>
        ∀ occurrence : state.base.Occurrence,
          package.currentAmbientEndpoint stage ∉
            P13ProducedPriorSupportLedger.eventSupport
              (state.base.event occurrence) := by
  unfold ProducedPriorD6State.recognizeF4
  cases result : (priorD6SupportProfile (ctx := ctx)).recognize state.baseState
      (package.currentAmbientEndpoint stage) with
  | found hit =>
      exact ⟨hit.occurrence_mem, hit.contains, hit.get .here⟩
  | absent absentProof => exact absentProof

theorem currentAmbientEndpoint_mem_prefixAmbientSupport
    (stage : package.Stage) :
    package.currentAmbientEndpoint stage ∈ package.prefixAmbientSupport stage := by
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  rw [prefixAmbientSupport, List.mem_toFinset, List.mem_map]
  refine ⟨(InducedPathRestrictedComponentBoundarySchedule.componentPath
      package.input).getVert stage.val, ?_, rfl⟩
  have endpointMem := (package.profile.prefixWalk stage).end_mem_support
  rw [package.profile.prefixWalk_support stage] at endpointMem
  exact endpointMem

/-- All thirteen literal vertices of one displayed cold-window interface. -/
noncomputable def displayedWindowSupport
    (_package : P13WeightedColdRestrictedPrefixPackage ctx node21)
    (window : InducedPathWindowLedger.WindowIndex ctx.G.object) :
    Finset ctx.G.Vertex := by
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  exact Finset.univ.image fun offset : Fin 13 =>
    selectedWindow ctx.G.object window offset

/-- The exact support observed at this stage: the growing literal prefix and
both complete displayed `P₁₃` window interfaces.  This set is finite but is
not asserted to have the manuscript's uniform `Q_cold` bound. -/
noncomputable def stageObservedSupport (stage : package.Stage) :
    Finset ctx.G.Vertex := by
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  exact package.prefixAmbientSupport stage ∪
    displayedWindowSupport package package.input.anchor.window ∪
    displayedWindowSupport package
      (InducedPathRestrictedComponentBoundarySchedule.successor
        package.input).window

set_option maxHeartbeats 800000 in
theorem currentAmbientEndpoint_mem_stageObservedSupport
    (stage : package.Stage) :
    package.currentAmbientEndpoint stage ∈ package.stageObservedSupport stage := by
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact package.currentAmbientEndpoint_mem_prefixAmbientSupport stage

theorem currentAmbientEndpoint_mem_boundedActiveInterface
    (stage : package.Stage) :
    package.currentAmbientEndpoint stage ∈ package.boundedActiveInterface stage := by
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  rw [boundedActiveInterface]
  apply Finset.mem_union_right
  change package.currentAmbientEndpoint stage ∈
    {package.input.anchor.neighbor,
      package.boundedInterfaceCurrentEndpoint stage}
  have endpointExact : package.currentAmbientEndpoint stage =
      package.boundedInterfaceCurrentEndpoint stage := rfl
  simp [endpointExact]

/-- Exact occurrence-indexed support view of the accumulated residual. -/
noncomputable def d6Profile (ledger : package.PriorD6Ledger) :=
  ledger.supportView

abbrev D6Key (ledger : package.PriorD6Ledger) :=
  ledger.baseState.residuals.Occurrence

noncomputable def d6Entry (ledger : package.PriorD6Ledger)
    (key : package.D6Key ledger) : package.PriorD6Event :=
  ledger.baseState.residuals.event key

abbrev D6Coordinate (ledger : package.PriorD6Ledger)
    (stage : package.Stage) :=
  (package.d6Profile ledger).ActiveOccurrence
    (package.boundedActiveInterface stage)

/-- Exactly all already-produced D6/F4 keys whose complete support lies in
the finite support observed at the current stage. -/
@[implicit_reducible] noncomputable def d6Coordinates
    (ledger : package.PriorD6Ledger) (stage : package.Stage) :
    FinEnum (package.D6Coordinate ledger stage) :=
  (package.d6Profile ledger).activeOccurrences
    (package.boundedActiveInterface stage)

inductive D6Kind
  | node64To65Ordinary
  | decoratedTypeBEnvelope
  | routeEightCarrier
  deriving DecidableEq, Repr, Fintype

@[implicit_reducible] def d6Kinds : FinEnum D6Kind :=
  FinEnum.ofNodupList [.node64To65Ordinary,
    .decoratedTypeBEnvelope, .routeEightCarrier]
    (by intro kind; cases kind <;> simp) (by simp)

noncomputable def d6Kind : package.PriorD6Event → D6Kind
  | .first _ => .node64To65Ordinary
  | .second _ => .decoratedTypeBEnvelope
  | .third _ => .routeEightCarrier

/-! ## Occurrence-free structural normalization of the prior ledger

The ledger key is an append occurrence and therefore cannot be part of a
uniform cut code.  The structural label below retains only the event family
and the exact subset of the fixed 28-role carrier occupied by its declared
support.  Repeated ledger occurrences with the same label are deliberately
identified.  This is a local scan of the already-produced ledger; it does not
enumerate ambient events or vertex subsets. -/

abbrev D6StructuralCode := D6Kind × (BoundedCarrierRole → Bool)

/-- Cardinality of the fixed structural alphabet.  This theorem is symbolic:
the runner never materializes the `2^28` support masks. -/
theorem d6StructuralCode_card :
    Fintype.card D6StructuralCode = 3 * 2 ^ 28 := by
  change Fintype.card (D6Kind ×
    ((Fin 13 ⊕ (Fin 13 ⊕ Bool)) → Bool)) = 3 * 2 ^ 28
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_sum,
    Fintype.card_fin, Fintype.card_bool]
  rw [show Fintype.card D6Kind = 3 by native_decide]

noncomputable def d6SupportRoleMask (stage : package.Stage)
    (event : package.PriorD6Event) : BoundedCarrierRole → Bool := by
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  exact fun role => decide
      (package.boundedCarrierRoleVertex stage role ∈
        P13ProducedPriorSupportLedger.eventSupport event)

noncomputable def d6StructuralCode (ledger : package.PriorD6Ledger)
    (stage : package.Stage) (coordinate : package.D6Coordinate ledger stage) :
    D6StructuralCode :=
  let event := package.d6Entry ledger coordinate.1
  (package.d6Kind event, package.d6SupportRoleMask stage event)

/-- Equality of occurrence-free labels recovers equality of the exact
graph-derived event kind and declared support.  Carrier collisions are safe:
the canonical first-role code names vertices, while the mask is evaluated on
all roles, so coincident roles receive the same membership bit. -/
theorem d6StructuralCode_eq_implies_kind_support_eq
    (ledger : package.PriorD6Ledger) (stage : package.Stage)
    (left right : package.D6Coordinate ledger stage)
    (equal : package.d6StructuralCode ledger stage left =
      package.d6StructuralCode ledger stage right) :
    package.d6Kind (package.d6Entry ledger left.1) =
        package.d6Kind (package.d6Entry ledger right.1) ∧
      P13ProducedPriorSupportLedger.eventSupport
          (package.d6Entry ledger left.1) =
        P13ProducedPriorSupportLedger.eventSupport
          (package.d6Entry ledger right.1) := by
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  constructor
  · exact congrArg Prod.fst equal
  · let leftEvent := package.d6Entry ledger left.1
    let rightEvent := package.d6Entry ledger right.1
    have masksEqual : package.d6SupportRoleMask stage leftEvent =
        package.d6SupportRoleMask stage rightEvent := congrArg Prod.snd equal
    apply Finset.ext
    intro vertex
    constructor
    · intro leftMember
      have carrierMember : vertex ∈ package.boundedActiveInterface stage :=
        left.2 leftMember
      obtain ⟨role, roleExact⟩ :=
        (package.mem_boundedActiveInterface_iff_role stage vertex).mp carrierMember
      have bitEqual := congrFun masksEqual role
      have leftTrue : decide
          (package.boundedCarrierRoleVertex stage role ∈
            P13ProducedPriorSupportLedger.eventSupport leftEvent) = true := by
        apply decide_eq_true
        simpa [roleExact, leftEvent] using leftMember
      have rightTrue : decide
          (package.boundedCarrierRoleVertex stage role ∈
            P13ProducedPriorSupportLedger.eventSupport rightEvent) = true := by
        calc
          decide (package.boundedCarrierRoleVertex stage role ∈
              P13ProducedPriorSupportLedger.eventSupport rightEvent) =
              decide (package.boundedCarrierRoleVertex stage role ∈
                P13ProducedPriorSupportLedger.eventSupport leftEvent) := by
            simpa [d6SupportRoleMask] using bitEqual.symm
          _ = true := leftTrue
      exact of_decide_eq_true (by simpa [roleExact, rightEvent] using rightTrue)
    · intro rightMember
      have carrierMember : vertex ∈ package.boundedActiveInterface stage :=
        right.2 rightMember
      obtain ⟨role, roleExact⟩ :=
        (package.mem_boundedActiveInterface_iff_role stage vertex).mp carrierMember
      have bitEqual := congrFun masksEqual role
      have rightTrue : decide
          (package.boundedCarrierRoleVertex stage role ∈
            P13ProducedPriorSupportLedger.eventSupport rightEvent) = true := by
        apply decide_eq_true
        simpa [roleExact, rightEvent] using rightMember
      have leftTrue : decide
          (package.boundedCarrierRoleVertex stage role ∈
            P13ProducedPriorSupportLedger.eventSupport leftEvent) = true := by
        calc
          decide (package.boundedCarrierRoleVertex stage role ∈
              P13ProducedPriorSupportLedger.eventSupport leftEvent) =
              decide (package.boundedCarrierRoleVertex stage role ∈
                P13ProducedPriorSupportLedger.eventSupport rightEvent) := by
            simpa [d6SupportRoleMask] using bitEqual
          _ = true := rightTrue
      exact of_decide_eq_true (by simpa [roleExact, leftEvent] using leftTrue)

/-- The graph-derived observation retained after quotienting occurrence
identity.  It is intentionally smaller than the proof-carrying event: D6
needs its family and complete declared support, while provenance remains in
the source ledger and F4 keeps the first literal occurrence. -/
structure D6StructuralValue where
  kind : D6Kind
  support : Finset ctx.G.Vertex

theorem D6StructuralValue.eq_of_kind_support_eq
    {left right : D6StructuralValue (ctx := ctx)}
    (kindEqual : left.kind = right.kind)
    (supportEqual : left.support = right.support) : left = right := by
  cases left with
  | mk leftKind leftSupport =>
      cases right with
      | mk rightKind rightSupport =>
          simp only [mk.injEq] at kindEqual supportEqual ⊢
          exact ⟨kindEqual, supportEqual⟩

noncomputable def d6StructuralValue (ledger : package.PriorD6Ledger)
    (stage : package.Stage) (coordinate : package.D6Coordinate ledger stage) :
    D6StructuralValue (ctx := ctx) where
  kind := package.d6Kind (package.d6Entry ledger coordinate.1)
  support := P13ProducedPriorSupportLedger.eventSupport
    (package.d6Entry ledger coordinate.1)

theorem d6StructuralCode_eq_implies_value_eq
    (ledger : package.PriorD6Ledger) (stage : package.Stage)
    (left right : package.D6Coordinate ledger stage)
    (equal : package.d6StructuralCode ledger stage left =
      package.d6StructuralCode ledger stage right) :
    package.d6StructuralValue ledger stage left =
      package.d6StructuralValue ledger stage right := by
  obtain ⟨kindEqual, supportEqual⟩ :=
    package.d6StructuralCode_eq_implies_kind_support_eq ledger stage left right equal
  exact D6StructuralValue.eq_of_kind_support_eq kindEqual supportEqual

/-- Exact normalized D6 alphabet actually used at one stage.  `dedup` is
applied only to the mapped produced ledger, never to an ambient universe. -/
noncomputable def normalizedD6StructuralCodes (ledger : package.PriorD6Ledger)
    (stage : package.Stage) : List D6StructuralCode := by
  classical
  exact ((package.d6Coordinates ledger stage).orderedValues.map
    (package.d6StructuralCode ledger stage)).dedup

theorem normalizedD6StructuralCodes_nodup (ledger : package.PriorD6Ledger)
    (stage : package.Stage) :
    (package.normalizedD6StructuralCodes ledger stage).Nodup := by
  classical
  exact List.nodup_dedup _

theorem normalizedD6StructuralCodes_length_le_fixed
    (ledger : package.PriorD6Ledger) (stage : package.Stage) :
    (package.normalizedD6StructuralCodes ledger stage).length ≤ 3 * 2 ^ 28 := by
  rw [← d6StructuralCode_card]
  exact (package.normalizedD6StructuralCodes_nodup ledger stage).length_le_card

theorem everyD6Occurrence_has_normalized_code
    (ledger : package.PriorD6Ledger) (stage : package.Stage)
    (coordinate : package.D6Coordinate ledger stage) :
    package.d6StructuralCode ledger stage coordinate ∈
      package.normalizedD6StructuralCodes ledger stage := by
  classical
  simp [normalizedD6StructuralCodes]

/-! ## Exact labelled D6 subcoordinates carried by prior events -/

abbrev DecoratedEntry :=
  TypeBProducedSupportLedgerConnector.RecordedDecoratedHandoff (ctx := ctx)

abbrev DecoratedFirstNeighbor (entry : DecoratedEntry (ctx := ctx)) :=
  Graph.TypeBDecoratedArmCoordinate.FirstNeighbor entry.handoff

abbrev DecoratedFanSafePair (entry : DecoratedEntry (ctx := ctx)) :=
  {pair : DecoratedFirstNeighbor entry × DecoratedFirstNeighbor entry //
    pair.1 ≠ pair.2}

abbrev DecoratedArmCoordinate (entry : DecoratedEntry (ctx := ctx)) :=
  Graph.TypeBDecoratedArmCoordinate.Coordinate entry.handoff

/-- Labels actually present at a decorated F4 producer: the whole envelope,
its center and source core, retained first neighbours, every distinct
fan-safe pair, and every stored arm position. -/
abbrev DecoratedD6Coordinate (entry : DecoratedEntry (ctx := ctx)) :=
  Unit ⊕ (Unit ⊕ (DecoratedFirstNeighbor entry ⊕
    (DecoratedFanSafePair entry ⊕ DecoratedArmCoordinate entry)))

@[implicit_reducible] noncomputable def decoratedFanSafePairs
    (entry : DecoratedEntry (ctx := ctx)) :
    FinEnum (DecoratedFanSafePair entry) := by
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  letI : FinEnum (DecoratedFirstNeighbor entry) :=
    Graph.TypeBDecoratedArmCoordinate.firstNeighbors entry.handoff
  let pairs : FinEnum
      (DecoratedFirstNeighbor entry × DecoratedFirstNeighbor entry) := by
    infer_instance
  exact Core.Enumeration.subtype pairs (fun pair => pair.1 ≠ pair.2)
    (fun pair => inferInstance)

@[implicit_reducible] noncomputable def decoratedD6Coordinates
    (entry : DecoratedEntry (ctx := ctx)) :
    FinEnum (DecoratedD6Coordinate entry) := by
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  letI : FinEnum (DecoratedFirstNeighbor entry) :=
    Graph.TypeBDecoratedArmCoordinate.firstNeighbors entry.handoff
  letI : FinEnum (DecoratedFanSafePair entry) := decoratedFanSafePairs entry
  letI : FinEnum (DecoratedArmCoordinate entry) :=
    Graph.TypeBDecoratedArmCoordinate.coordinates entry.handoff
  infer_instance

noncomputable def decoratedD6Support (entry : DecoratedEntry (ctx := ctx)) :
    DecoratedD6Coordinate entry → Finset ctx.G.Vertex := by
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  intro coordinate
  rcases coordinate with _ | (_ | (first | (pair | arm)))
  · exact entry.declaredSupport
  · exact {entry.handoff.center}
  · exact {entry.handoff.center, first.1}
  · exact insert entry.handoff.center
      (insert pair.1.1.1 {pair.1.2.1})
  · exact Graph.TypeBDecoratedArmCoordinate.Coordinate.support
      entry.handoff arm

/-- Each local decorated label is evaluated from the stored graph payload.
These are precisely the semantics needed before entering the later Type-B
fan-window machinery. -/
inductive DecoratedD6Semantics (entry : DecoratedEntry (ctx := ctx)) :
    DecoratedD6Coordinate entry → Prop
  | envelope : entry.source.core ⊆ entry.declaredSupport →
      DecoratedD6Semantics entry (.inl ())
  | center : 4 ≤ ctx.G.object.degree entry.handoff.center →
      DecoratedD6Semantics entry (.inr (.inl ()))
  | firstNeighbor (first : DecoratedFirstNeighbor entry) :
      ctx.G.object.graph.Adj entry.handoff.center first.1 →
      DecoratedD6Semantics entry (.inr (.inr (.inl first)))
  | fanSafePair (pair : DecoratedFanSafePair entry) :
      entry.FanSafe entry.handoff.center pair.1.1.1 pair.1.2.1 →
      DecoratedD6Semantics entry (.inr (.inr (.inr (.inl pair))))
  | arm (coordinate : DecoratedArmCoordinate entry) :
      (entry.handoff.arm coordinate.first).path.IsPath →
      entry.handoff.center ∉
        (entry.handoff.arm coordinate.first).path.support →
      DecoratedD6Semantics entry (.inr (.inr (.inr (.inr coordinate))))

theorem decoratedD6Semantics
    (entry : DecoratedEntry (ctx := ctx))
    (coordinate : DecoratedD6Coordinate entry) :
    DecoratedD6Semantics entry coordinate := by
  cases coordinate with
  | inl _ =>
      exact .envelope entry.source_core_subset_declaredSupport
  | inr rest =>
      cases rest with
      | inl _ => exact .center entry.handoff.center_high
      | inr rest =>
          cases rest with
          | inl first =>
              apply DecoratedD6Semantics.firstNeighbor first
              rw [← entry.handoff.arm_first first]
              exact (entry.handoff.arm first).center_adjacent
          | inr rest =>
              cases rest with
              | inl pair =>
                  apply DecoratedD6Semantics.fanSafePair pair
                  exact Graph.TypeBDecoratedArmCoordinate.retained_pair_fanSafe
                    entry.handoff pair.1.1 pair.1.2 pair.2
              | inr arm =>
                  exact .arm arm
                    (Graph.TypeBDecoratedArmCoordinate.Coordinate.arm_isPath
                      entry.handoff arm)
                    (Graph.TypeBDecoratedArmCoordinate.Coordinate.center_not_mem_arm
                      entry.handoff arm)

/-- Distinct decorated fan-response labels carried by the handoff itself:
the center boundary-degree response and one terminal response for every
retained arm. -/
abbrev DecoratedFanResponseCoordinate
    (entry : DecoratedEntry (ctx := ctx)) :=
  Unit ⊕ DecoratedFirstNeighbor entry

@[implicit_reducible] noncomputable def decoratedFanResponseCoordinates
    (entry : DecoratedEntry (ctx := ctx)) :
    FinEnum (DecoratedFanResponseCoordinate entry) := by
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  letI : FinEnum (DecoratedFirstNeighbor entry) :=
    Graph.TypeBDecoratedArmCoordinate.firstNeighbors entry.handoff
  infer_instance

noncomputable def decoratedFanResponseSupport
    (entry : DecoratedEntry (ctx := ctx)) :
    DecoratedFanResponseCoordinate entry → Finset ctx.G.Vertex := by
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  intro coordinate
  cases coordinate with
  | inl _ => exact {entry.handoff.center}
  | inr first =>
      exact insert entry.handoff.center
        (entry.handoff.arm first).path.support.toFinset

inductive DecoratedFanResponseValue
    (entry : DecoratedEntry (ctx := ctx)) :
    DecoratedFanResponseCoordinate entry → Type u
  | boundaryDegree :
      (degree : Nat) →
      degree = ctx.G.object.degree entry.handoff.center →
      DecoratedFanResponseValue entry (.inl ())
  | armTerminal (first : DecoratedFirstNeighbor entry) :
      (terminal : ctx.G.Vertex) →
      terminal = (entry.handoff.arm first).terminal →
      terminal ∈ entry.source.core →
      DecoratedFanResponseValue entry (.inr first)

noncomputable def decoratedFanResponseValue
    (entry : DecoratedEntry (ctx := ctx))
    (coordinate : DecoratedFanResponseCoordinate entry) :
    DecoratedFanResponseValue entry coordinate := by
  cases coordinate with
  | inl _ =>
      exact .boundaryDegree (ctx.G.object.degree entry.handoff.center) rfl
  | inr first =>
      exact .armTerminal first (entry.handoff.arm first).terminal rfl
        (entry.handoff.arm first).terminal_mem

/-- The ordinary Type-B producer contributes its exact high center on the
existing `[64] -> [65]` edge. -/
inductive OrdinaryD6Coordinate
    (_entry : P13ProducedPriorSupportLedger.Node64To65Ordinary (ctx := ctx)) :
    Type u where
  | center
  deriving DecidableEq

@[implicit_reducible] def ordinaryD6Coordinates
    (entry : P13ProducedPriorSupportLedger.Node64To65Ordinary (ctx := ctx)) :
    FinEnum (OrdinaryD6Coordinate entry) :=
  FinEnum.ofNodupList [.center]
    (by intro coordinate; cases coordinate; simp) (by simp)

/-- The route-8 producer already stores its exact carrier core.  It has one
composite F4/D6 support key; later Type-A route-8 coordinates remain owned by
their downstream branch. -/
inductive RouteEightD6Coordinate
    (_entry : P13ProducedPriorSupportLedger.RecordedRouteEightExtraction
      (ctx := ctx)) : Type u where
  | carrier

noncomputable instance
    (entry : P13ProducedPriorSupportLedger.RecordedRouteEightExtraction
      (ctx := ctx)) : DecidableEq (RouteEightD6Coordinate entry) :=
  Classical.decEq _

@[implicit_reducible] noncomputable def routeEightD6Coordinates
    (entry : P13ProducedPriorSupportLedger.RecordedRouteEightExtraction
      (ctx := ctx)) : FinEnum (RouteEightD6Coordinate entry) :=
  FinEnum.ofNodupList [.carrier]
    (by intro coordinate; cases coordinate; simp) (by simp)

def EventD6Coordinate : package.PriorD6Event → Type _
  | .first entry => OrdinaryD6Coordinate entry
  | .second entry =>
      DecoratedD6Coordinate entry ⊕ DecoratedFanResponseCoordinate entry
  | .third entry => RouteEightD6Coordinate entry

/-- Literal observation attached to each decorated base label.  The label is
dependent, so equal vertices or numbers in different families never collapse. -/
inductive DecoratedD6Observation (entry : DecoratedEntry (ctx := ctx)) :
    DecoratedD6Coordinate entry → Type u
  | envelope (support : Finset ctx.G.Vertex) :
      DecoratedD6Observation entry (.inl ())
  | center (degree : Nat) :
      DecoratedD6Observation entry (.inr (.inl ()))
  | firstNeighbor (first : DecoratedFirstNeighbor entry)
      (center neighbor : ctx.G.Vertex) :
      DecoratedD6Observation entry (.inr (.inr (.inl first)))
  | fanSafePair (pair : DecoratedFanSafePair entry)
      (center left right : ctx.G.Vertex) :
      DecoratedD6Observation entry (.inr (.inr (.inr (.inl pair))))
  | arm (coordinate : DecoratedArmCoordinate entry)
      (value : coordinate.Value entry.handoff) :
      DecoratedD6Observation entry (.inr (.inr (.inr (.inr coordinate))))

noncomputable def decoratedD6Observation
    (entry : DecoratedEntry (ctx := ctx))
    (coordinate : DecoratedD6Coordinate entry) :
    DecoratedD6Observation entry coordinate := by
  rcases coordinate with _ | (_ | (first | (pair | arm)))
  · exact .envelope entry.declaredSupport
  · exact .center (ctx.G.object.degree entry.handoff.center)
  · exact .firstNeighbor first entry.handoff.center first.1
  · exact .fanSafePair pair entry.handoff.center pair.1.1.1 pair.1.2.1
  · exact .arm arm
      (Graph.TypeBDecoratedArmCoordinate.Coordinate.value entry.handoff arm)

/-- Exact value of one decorated base coordinate: declared support, literal
observation and the already-proved graph semantics are retained together. -/
structure DecoratedD6ExactValue (entry : DecoratedEntry (ctx := ctx))
    (coordinate : DecoratedD6Coordinate entry) where
  support : Finset ctx.G.Vertex
  supportExact : support = decoratedD6Support entry coordinate
  observation : DecoratedD6Observation entry coordinate
  observationExact : observation = decoratedD6Observation entry coordinate
  semantics : DecoratedD6Semantics entry coordinate

noncomputable def decoratedD6ExactValue
    (entry : DecoratedEntry (ctx := ctx))
    (coordinate : DecoratedD6Coordinate entry) :
    DecoratedD6ExactValue entry coordinate where
  support := decoratedD6Support entry coordinate
  supportExact := rfl
  observation := decoratedD6Observation entry coordinate
  observationExact := rfl
  semantics := decoratedD6Semantics entry coordinate

/-- Exact D6 center value on the existing ordinary `[64] -> [65]` input.
The high-degree fact is retained from node [62] through node [64]. -/
structure OrdinaryD6ExactValue
    (entry : P13ProducedPriorSupportLedger.Node64To65Ordinary (ctx := ctx))
    (_coordinate : OrdinaryD6Coordinate entry) where
  center : ctx.G.Vertex
  centerExact : center = entry.highSurplus.center
  high : 4 ≤ ctx.G.object.degree center

noncomputable def ordinaryD6ExactValue
    (entry : P13ProducedPriorSupportLedger.Node64To65Ordinary (ctx := ctx))
    (coordinate : OrdinaryD6Coordinate entry) :
    OrdinaryD6ExactValue entry coordinate :=
  ⟨entry.highSurplus.center, rfl,
    P13ProducedPriorSupportLedger.Node64To65Ordinary.center_high entry⟩

/-- Route-8's currently produced D6 label is its exact carrier core. -/
structure RouteEightD6ExactValue
    (entry : P13ProducedPriorSupportLedger.RecordedRouteEightExtraction
      (ctx := ctx)) (_coordinate : RouteEightD6Coordinate entry) where
  carrier : Finset ctx.G.Vertex
  carrierExact : carrier = entry.declaredSupport

noncomputable def routeEightD6ExactValue
    (entry : P13ProducedPriorSupportLedger.RecordedRouteEightExtraction
      (ctx := ctx)) (coordinate : RouteEightD6Coordinate entry) :
    RouteEightD6ExactValue entry coordinate :=
  ⟨entry.declaredSupport, rfl⟩

/-- Exact dependent value for every D6 subcoordinate actually present in a
produced event.  The value is the producer's literal value; no application
wrapper or second event eliminator is introduced. -/
noncomputable def EventD6ExactValue (event : package.PriorD6Event)
    (coordinate : package.EventD6Coordinate event) : Type u := by
  cases event with
  | first entry => exact OrdinaryD6ExactValue entry coordinate
  | second entry =>
      change DecoratedD6Coordinate entry ⊕
        DecoratedFanResponseCoordinate entry at coordinate
      cases coordinate with
      | inl base => exact DecoratedD6ExactValue entry base
      | inr response => exact DecoratedFanResponseValue entry response
  | third entry => exact RouteEightD6ExactValue entry coordinate

noncomputable def eventD6ExactValue (event : package.PriorD6Event)
    (coordinate : package.EventD6Coordinate event) :
    package.EventD6ExactValue event coordinate := by
  cases event with
  | first entry =>
      exact ordinaryD6ExactValue entry coordinate
  | second entry =>
      change DecoratedD6Coordinate entry ⊕
        DecoratedFanResponseCoordinate entry at coordinate
      cases coordinate with
      | inl base =>
          exact decoratedD6ExactValue entry base
      | inr response =>
          exact decoratedFanResponseValue entry response
  | third entry =>
      exact routeEightD6ExactValue entry coordinate

@[implicit_reducible] noncomputable def eventD6Coordinates
    (event : package.PriorD6Event) : FinEnum (package.EventD6Coordinate event) := by
  cases event with
  | first entry => exact ordinaryD6Coordinates entry
  | second entry =>
      letI : FinEnum (DecoratedD6Coordinate entry) := decoratedD6Coordinates entry
      letI : FinEnum (DecoratedFanResponseCoordinate entry) :=
        decoratedFanResponseCoordinates entry
      change FinEnum
        (DecoratedD6Coordinate entry ⊕ DecoratedFanResponseCoordinate entry)
      infer_instance
  | third entry => exact routeEightD6Coordinates entry

noncomputable def eventD6Support (event : package.PriorD6Event) :
    package.EventD6Coordinate event → Finset ctx.G.Vertex := by
  cases event with
  | first entry => exact fun _ => entry.declaredSupport
  | second entry =>
      intro coordinate
      change DecoratedD6Coordinate entry ⊕
        DecoratedFanResponseCoordinate entry at coordinate
      cases coordinate with
      | inl baseCoordinate => exact decoratedD6Support entry baseCoordinate
      | inr response => exact decoratedFanResponseSupport entry response
  | third entry => exact fun _ => entry.declaredSupport

abbrev RawDeclaredD6Coordinate (ledger : package.PriorD6Ledger) :=
  Sigma fun key : package.D6Key ledger =>
    package.EventD6Coordinate (package.d6Entry ledger key)

def RawDeclaredD6ExactValue (ledger : package.PriorD6Ledger) :
    package.RawDeclaredD6Coordinate ledger → Type u
  | ⟨key, coordinate⟩ =>
      package.EventD6ExactValue (package.d6Entry ledger key) coordinate

noncomputable def rawDeclaredD6ExactValue (ledger : package.PriorD6Ledger)
    (coordinate : package.RawDeclaredD6Coordinate ledger) :
    package.RawDeclaredD6ExactValue ledger coordinate :=
  package.eventD6ExactValue
    (package.d6Entry ledger coordinate.1) coordinate.2

abbrev ExactDeclaredD6Entry (ledger : package.PriorD6Ledger) :=
  Sigma fun coordinate : package.RawDeclaredD6Coordinate ledger =>
    package.RawDeclaredD6ExactValue ledger coordinate

noncomputable def exactDeclaredD6Entry (ledger : package.PriorD6Ledger)
    (coordinate : package.RawDeclaredD6Coordinate ledger) :
    package.ExactDeclaredD6Entry ledger :=
  ⟨coordinate, package.rawDeclaredD6ExactValue ledger coordinate⟩

@[implicit_reducible] noncomputable def rawDeclaredD6Coordinates
    (ledger : package.PriorD6Ledger) :
    FinEnum (package.RawDeclaredD6Coordinate ledger) := by
  letI : FinEnum (package.D6Key ledger) :=
    ledger.baseState.residuals.occurrences
  letI : (key : package.D6Key ledger) → FinEnum
      (package.EventD6Coordinate (package.d6Entry ledger key)) :=
    fun key => package.eventD6Coordinates (package.d6Entry ledger key)
  infer_instance

noncomputable def rawDeclaredD6Support (ledger : package.PriorD6Ledger)
    (coordinate : package.RawDeclaredD6Coordinate ledger) :
    Finset ctx.G.Vertex :=
  package.eventD6Support (package.d6Entry ledger coordinate.1)
    coordinate.2

def DeclaredD6SupportedIn (ledger : package.PriorD6Ledger)
    (stage : package.Stage) (coordinate : package.RawDeclaredD6Coordinate ledger) :
    Prop := package.rawDeclaredD6Support ledger coordinate ⊆
      package.boundedActiveInterface stage

noncomputable def declaredD6SupportedInDecidable
    (ledger : package.PriorD6Ledger) (stage : package.Stage)
    (coordinate : package.RawDeclaredD6Coordinate ledger) :
    Decidable (package.DeclaredD6SupportedIn ledger stage coordinate) := by
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  unfold DeclaredD6SupportedIn
  infer_instance

abbrev DeclaredD6Coordinate (ledger : package.PriorD6Ledger)
    (stage : package.Stage) :=
  {coordinate : package.RawDeclaredD6Coordinate ledger //
    package.DeclaredD6SupportedIn ledger stage coordinate}

/-- Exact finite labelled D6 coordinate family on the observed stage support. -/
@[implicit_reducible] noncomputable def declaredD6Coordinates
    (ledger : package.PriorD6Ledger) (stage : package.Stage) :
    FinEnum (package.DeclaredD6Coordinate ledger stage) :=
  Core.Enumeration.subtype (package.rawDeclaredD6Coordinates ledger)
    (package.DeclaredD6SupportedIn ledger stage)
    (package.declaredD6SupportedInDecidable ledger stage)

theorem declaredD6Coordinates_complete (ledger : package.PriorD6Ledger)
    (stage : package.Stage)
    (coordinate : package.RawDeclaredD6Coordinate ledger)
    (contained : package.rawDeclaredD6Support ledger coordinate ⊆
      package.boundedActiveInterface stage) :
    ∃ retained : package.DeclaredD6Coordinate ledger stage,
      retained.1 = coordinate :=
  ⟨⟨coordinate, contained⟩, rfl⟩

theorem declaredD6Coordinates_card_le_raw (ledger : package.PriorD6Ledger)
    (stage : package.Stage) :
    (package.declaredD6Coordinates ledger stage).card ≤
      (package.rawDeclaredD6Coordinates ledger).card :=
  Core.Enumeration.subtype_card_le (package.rawDeclaredD6Coordinates ledger)
    (package.DeclaredD6SupportedIn ledger stage)
    (package.declaredD6SupportedInDecidable ledger stage)

/-! ## Fixed carrier-role normalization of the dependent D6 family

The ambient degree of a decoration center is deliberately absent here.  It is
part of the separately retained D1 boundary-degree fibre, not a D6 value in
the embedded support.  Including it here would make `Q_cold` depend on the
ambient graph.  D6 retains the exact structural data prescribed by clause D6:
the family, its semantic label, complete support, and its embedded local
value.  Every proposition-valued response below is already proved by its
producer, so `none` is its unique true value; arm-position and terminal values
carry the corresponding canonical carrier role.
-/

abbrev D6DeclaredKindCode := Fin 9

abbrev D6DeclaredLabelCode :=
  BoundedCarrierRole ⊕
  (BoundedCarrierRole ⊕
  ((BoundedCarrierRole × BoundedCarrierRole) ⊕
  ((BoundedCarrierRole × BoundedCarrierRole × BoundedCarrierRole) ⊕
  ((BoundedCarrierRole × BoundedCarrierRole × Fin 28) ⊕
  (BoundedCarrierRole ⊕
  ((BoundedCarrierRole × BoundedCarrierRole) ⊕ Unit))))))

abbrev D6DeclaredValueCode := Option BoundedCarrierRole

noncomputable instance d6DeclaredLabelCodeDecidableEq :
    DecidableEq D6DeclaredLabelCode := Classical.decEq _

def d6EnvelopeLabel (center : BoundedCarrierRole) : D6DeclaredLabelCode :=
  .inl center

def d6CenterLabel (center : BoundedCarrierRole) : D6DeclaredLabelCode :=
  .inr (.inl center)

def d6FirstNeighborLabel (center first : BoundedCarrierRole) :
    D6DeclaredLabelCode :=
  .inr (.inr (.inl (center, first)))

def d6FanSafePairLabel (center left right : BoundedCarrierRole) :
    D6DeclaredLabelCode :=
  .inr (.inr (.inr (.inl (center, left, right))))

def d6ArmLabel (center first : BoundedCarrierRole) (position : Fin 28) :
    D6DeclaredLabelCode :=
  .inr (.inr (.inr (.inr (.inl (center, first, position)))))

def d6FanResponseLabel (center : BoundedCarrierRole) : D6DeclaredLabelCode :=
  .inr (.inr (.inr (.inr (.inr (.inl center)))))

def d6ArmTerminalLabel (center first : BoundedCarrierRole) :
    D6DeclaredLabelCode :=
  .inr (.inr (.inr (.inr (.inr (.inr (.inl (center, first)))))))

def d6RouteEightLabel : D6DeclaredLabelCode :=
  .inr (.inr (.inr (.inr (.inr (.inr (.inr ()))))))

noncomputable def d6CarrierRole (stage : package.Stage)
    (vertex : ctx.G.Vertex)
    (member : vertex ∈ package.boundedActiveInterface stage) :
    BoundedCarrierRole :=
  (package.boundedCarrierCode stage vertex member).role

theorem d6CarrierRole_injective (stage : package.Stage)
    {left right : ctx.G.Vertex}
    (leftMem : left ∈ package.boundedActiveInterface stage)
    (rightMem : right ∈ package.boundedActiveInterface stage)
    (equal : package.d6CarrierRole stage left leftMem =
      package.d6CarrierRole stage right rightMem) : left = right :=
  package.boundedCarrierCode_injective stage leftMem rightMem equal

noncomputable def eventD6KindCode (event : package.PriorD6Event)
    (coordinate : package.EventD6Coordinate event) : D6DeclaredKindCode := by
  cases event with
  | first entry => exact 0
  | second entry =>
      change DecoratedD6Coordinate entry ⊕
        DecoratedFanResponseCoordinate entry at coordinate
      rcases coordinate with base | response
      · rcases base with _ | (_ | (first | (pair | arm)))
        · exact 1
        · exact 2
        · exact 3
        · exact 4
        · exact 5
      · rcases response with _ | first
        · exact 6
        · exact 7
  | third entry => exact 8

theorem decoratedArmPosition_lt_28
    (entry : DecoratedEntry (ctx := ctx))
    (coordinate : DecoratedArmCoordinate entry)
    (supported : decoratedD6Support entry
      (.inr (.inr (.inr (.inr coordinate)))) ⊆
        package.boundedActiveInterface stage) :
    coordinate.position entry.handoff < 28 := by
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  have pathSubset :
      (entry.handoff.arm coordinate.first).path.support.toFinset ⊆
      package.boundedActiveInterface stage := by
    intro vertex member
    apply supported
    exact Finset.mem_insert_of_mem member
  have cardLe :
      (entry.handoff.arm coordinate.first).path.support.toFinset.card ≤
      (package.boundedActiveInterface stage).card :=
    Finset.card_le_card pathSubset
  have supportCard :
      (entry.handoff.arm coordinate.first).path.support.toFinset.card =
        (entry.handoff.arm coordinate.first).path.support.length :=
    List.toFinset_card_of_nodup
      (Graph.TypeBDecoratedArmCoordinate.Coordinate.arm_isPath
        entry.handoff coordinate).support_nodup
  have supportLe :
      (entry.handoff.arm coordinate.first).path.support.length ≤ 28 := by
    rw [← supportCard]
    exact cardLe.trans (package.boundedActiveInterface_card_le_28 stage)
  have positionLt : coordinate.position entry.handoff <
      (entry.handoff.arm coordinate.first).path.support.length := by
    rw [(entry.handoff.arm coordinate.first).path.length_support]
    change coordinate.2.1 <
      (entry.handoff.arm coordinate.1).path.length + 1
    exact coordinate.2.2
  exact positionLt.trans_le supportLe

noncomputable def eventD6LabelCode (stage : package.Stage)
    (event : package.PriorD6Event)
    (coordinate : package.EventD6Coordinate event)
    (supported : package.eventD6Support event coordinate ⊆
      package.boundedActiveInterface stage) : D6DeclaredLabelCode := by
  let role (vertex : ctx.G.Vertex)
      (member : vertex ∈ package.eventD6Support event coordinate) :=
    package.d6CarrierRole stage vertex (supported member)
  cases event with
  | first entry =>
      exact d6CenterLabel (role entry.highSurplus.center (by
        simp [eventD6Support,
          P13ProducedPriorSupportLedger.Node64To65Ordinary.center_mem_declaredSupport]))
  | second entry =>
          change DecoratedD6Coordinate entry ⊕
            DecoratedFanResponseCoordinate entry at coordinate
          rcases coordinate with base | response
          · rcases base with _ | (_ | (first | (pair | arm)))
            · exact d6EnvelopeLabel (role entry.handoff.center (by
                simp [eventD6Support, decoratedD6Support,
                  entry.center_mem_declaredSupport]))
            · exact d6CenterLabel (role entry.handoff.center (by
                simp [eventD6Support, decoratedD6Support]))
            · exact d6FirstNeighborLabel
                (role entry.handoff.center (by
                    simp [eventD6Support, decoratedD6Support]))
                (role first.1 (by simp [eventD6Support, decoratedD6Support]))
            · exact d6FanSafePairLabel
                (role entry.handoff.center (by
                    simp [eventD6Support, decoratedD6Support]))
                (role pair.1.1.1 (by simp [eventD6Support, decoratedD6Support]))
                (role pair.1.2.1 (by simp [eventD6Support, decoratedD6Support]))
            · exact d6ArmLabel
                (role entry.handoff.center (by
                    simp [eventD6Support, decoratedD6Support,
                      Graph.TypeBDecoratedArmCoordinate.Coordinate.support]))
                (role arm.first.1 (by
                    simp [eventD6Support, decoratedD6Support,
                      Graph.TypeBDecoratedArmCoordinate.Coordinate.support,
                      ← entry.handoff.arm_first arm.first,
                      (entry.handoff.arm arm.first).path.start_mem_support]))
                ⟨arm.position entry.handoff,
                  package.decoratedArmPosition_lt_28 entry arm (by
                    simpa [eventD6Support] using supported)⟩
          · rcases response with _ | first
            · exact d6FanResponseLabel
                (role entry.handoff.center (by
                  simp [eventD6Support, decoratedFanResponseSupport]))
            · exact d6ArmTerminalLabel
                (role entry.handoff.center (by
                    simp [eventD6Support, decoratedFanResponseSupport]))
                (role first.1 (by
                    simp [eventD6Support, decoratedFanResponseSupport,
                      ← entry.handoff.arm_first first,
                      (entry.handoff.arm first).path.start_mem_support]))
  | third entry => exact d6RouteEightLabel

noncomputable def eventD6ValueCode (stage : package.Stage)
    (event : package.PriorD6Event)
    (coordinate : package.EventD6Coordinate event)
    (supported : package.eventD6Support event coordinate ⊆
      package.boundedActiveInterface stage) : D6DeclaredValueCode := by
  let role (vertex : ctx.G.Vertex)
      (member : vertex ∈ package.eventD6Support event coordinate) :=
    package.d6CarrierRole stage vertex (supported member)
  cases event with
  | first entry => exact none
  | second entry =>
          change DecoratedD6Coordinate entry ⊕
            DecoratedFanResponseCoordinate entry at coordinate
          rcases coordinate with base | response
          · rcases base with _ | (_ | (first | (pair | arm)))
            · exact none
            · exact none
            · exact none
            · exact none
            · exact some (role (arm.vertex entry.handoff) (by
                exact Graph.TypeBDecoratedArmCoordinate.Coordinate.vertex_mem_support
                  entry.handoff arm))
          · rcases response with _ | first
            · exact none
            · exact some (role (entry.handoff.arm first).terminal (by
                simp [eventD6Support, decoratedFanResponseSupport]))
  | third entry => exact none

noncomputable def declaredD6NormalizationProfile
    (ledger : package.PriorD6Ledger) (stage : package.Stage) :
    Core.FiniteRoleSupportNormalization.Profile
      BoundedCarrierRole ctx.G.Vertex D6DeclaredKindCode
      D6DeclaredLabelCode D6DeclaredValueCode
      (package.DeclaredD6Coordinate ledger stage) where
  roles := package.boundedCarrierRoles
  vertexDecEq := ctx.G.object.input.vertices.decEq
  roleVertex := package.boundedCarrierRoleVertex stage
  carrier := package.boundedActiveInterface stage
  memCarrier_iff_role := package.mem_boundedActiveInterface_iff_role stage
  coordinates := package.declaredD6Coordinates ledger stage
  kind coordinate := package.eventD6KindCode
    (package.d6Entry ledger coordinate.1.1) coordinate.1.2
  label coordinate := package.eventD6LabelCode stage
    (package.d6Entry ledger coordinate.1.1) coordinate.1.2 coordinate.2
  support coordinate := package.rawDeclaredD6Support ledger coordinate.1
  supportContained coordinate := coordinate.2
  value coordinate := package.eventD6ValueCode stage
    (package.d6Entry ledger coordinate.1.1) coordinate.1.2 coordinate.2

abbrev D6DeclaredStructuralCode :=
  Core.FiniteRoleSupportNormalization.Profile.Code
    BoundedCarrierRole D6DeclaredKindCode D6DeclaredLabelCode D6DeclaredValueCode

theorem d6DeclaredStructuralCode_card :
    Fintype.card D6DeclaredStructuralCode =
      Fintype.card D6DeclaredKindCode * Fintype.card D6DeclaredLabelCode *
        2 ^ 28 * Fintype.card D6DeclaredValueCode := by
  simpa using
    (Core.FiniteRoleSupportNormalization.Profile.code_card
      (Role := BoundedCarrierRole) (Kind := D6DeclaredKindCode)
      (Label := D6DeclaredLabelCode) (Value := D6DeclaredValueCode))

noncomputable def d6DeclaredStructuralCode
    (ledger : package.PriorD6Ledger) (stage : package.Stage)
    (coordinate : package.DeclaredD6Coordinate ledger stage) :
    D6DeclaredStructuralCode :=
  (package.declaredD6NormalizationProfile ledger stage).code coordinate

noncomputable def normalizedD6DeclaredStructuralCodes
    (ledger : package.PriorD6Ledger) (stage : package.Stage) :
    List D6DeclaredStructuralCode :=
  (package.declaredD6NormalizationProfile ledger stage).normalizedCodes

theorem normalizedD6DeclaredStructuralCodes_nodup
    (ledger : package.PriorD6Ledger) (stage : package.Stage) :
    (package.normalizedD6DeclaredStructuralCodes ledger stage).Nodup :=
  (package.declaredD6NormalizationProfile ledger stage).normalizedCodes_nodup

theorem everyDeclaredD6Coordinate_has_normalizedCode
    (ledger : package.PriorD6Ledger) (stage : package.Stage)
    (coordinate : package.DeclaredD6Coordinate ledger stage) :
    package.d6DeclaredStructuralCode ledger stage coordinate ∈
      package.normalizedD6DeclaredStructuralCodes ledger stage :=
  by
    simpa [d6DeclaredStructuralCode, normalizedD6DeclaredStructuralCodes] using
      (package.declaredD6NormalizationProfile ledger stage)
        |>.every_coordinate_has_normalizedCode coordinate

theorem d6DeclaredStructuralCode_eq_implies_exact_tuple_eq
    (ledger : package.PriorD6Ledger) (stage : package.Stage)
    {left right : package.DeclaredD6Coordinate ledger stage}
    (equal : package.d6DeclaredStructuralCode ledger stage left =
      package.d6DeclaredStructuralCode ledger stage right) :
    (package.declaredD6NormalizationProfile ledger stage).structuralValue left =
      (package.declaredD6NormalizationProfile ledger stage).structuralValue right :=
  (package.declaredD6NormalizationProfile ledger stage)
    |>.code_eq_implies_structuralValue_eq equal

theorem normalizedD6DeclaredStructuralCodes_length_le_fixed
    (ledger : package.PriorD6Ledger) (stage : package.Stage) :
    (package.normalizedD6DeclaredStructuralCodes ledger stage).length ≤
      Fintype.card D6DeclaredKindCode * Fintype.card D6DeclaredLabelCode *
        2 ^ 28 * Fintype.card D6DeclaredValueCode := by
  simpa [normalizedD6DeclaredStructuralCodes] using
    (package.declaredD6NormalizationProfile ledger stage)
      |>.normalizedCodes_length_le_symbolic

/-- Graph-derived value of one retained D6 coordinate.  The exact event is
kept, rather than compressed to a Boolean. -/
structure D6Value (ledger : package.PriorD6Ledger)
    (stage : package.Stage) (coordinate : package.D6Coordinate ledger stage) where
  event : package.PriorD6Event
  eventExact : event = package.d6Entry ledger coordinate.1
  kind : D6Kind
  kindExact : kind = package.d6Kind event
  support : Finset ctx.G.Vertex
  supportExact : support = P13ProducedPriorSupportLedger.eventSupport event
  supportContained : support ⊆ package.boundedActiveInterface stage

noncomputable def d6Value (ledger : package.PriorD6Ledger)
    (stage : package.Stage) (coordinate : package.D6Coordinate ledger stage) :
    package.D6Value ledger stage coordinate where
  event := package.d6Entry ledger coordinate.1
  eventExact := rfl
  kind := package.d6Kind (package.d6Entry ledger coordinate.1)
  kindExact := rfl
  support := P13ProducedPriorSupportLedger.eventSupport
    (package.d6Entry ledger coordinate.1)
  supportExact := rfl
  supportContained := coordinate.2

/-- Completeness is literal: every produced key supported inside the active
interface occurs in the finite D6 coordinate type. -/
theorem d6Coordinates_complete (ledger : package.PriorD6Ledger)
    (stage : package.Stage) (key : package.D6Key ledger)
    (contained : P13ProducedPriorSupportLedger.eventSupport
      (package.d6Entry ledger key) ⊆ package.boundedActiveInterface stage) :
    ∃ coordinate : package.D6Coordinate ledger stage, coordinate.1 = key :=
  ((package.d6Profile ledger).mem_activeOccurrences_iff
    (package.boundedActiveInterface stage) key).mp contained

/-- Exact F4 output: one prior producer event, current-endpoint membership,
and absence of every earlier ledger key. -/
structure D6F4Hit (ledger : package.PriorD6Ledger)
    (stage : package.Stage) where
  hit : Graph.FiniteResidualSupportLedger.View.FirstHit
    (package.d6Profile ledger) (package.currentAmbientEndpoint stage)
  event : package.PriorD6Event
  eventExact : event = package.d6Entry ledger hit.occurrence
  occurrenceMem : hit.occurrence ∈ ledger.baseState.residuals.entries
  endpointMem : package.currentAmbientEndpoint stage ∈
    P13ProducedPriorSupportLedger.eventSupport event
  noEarlier : ∀ key ∈ hit.before,
    package.currentAmbientEndpoint stage ∉
      P13ProducedPriorSupportLedger.eventSupport
        (package.d6Entry ledger key)

noncomputable def d6F4Hit (ledger : package.PriorD6Ledger)
    (stage : package.Stage)
    (hit : Graph.FiniteResidualSupportLedger.View.FirstHit
      (package.d6Profile ledger) (package.currentAmbientEndpoint stage)) :
    package.D6F4Hit ledger stage where
  hit := hit
  event := package.d6Entry ledger hit.occurrence
  eventExact := rfl
  occurrenceMem := hit.occurrence_mem _ _
  endpointMem := by
    change package.currentAmbientEndpoint stage ∈
      (package.d6Profile ledger).support hit.occurrence
    exact hit.vertexMember
  noEarlier := hit.beforeAbsent

theorem D6F4Hit.exact_typeB_or_routeEight
    {package : P13WeightedColdRestrictedPrefixPackage ctx node21}
    {ledger : package.PriorD6Ledger} {stage : package.Stage}
    (hit : package.D6F4Hit ledger stage) :
    ((∃ entry : P13ProducedPriorSupportLedger.Node64To65Ordinary (ctx := ctx),
        hit.event = .first entry) ∨
      (∃ entry : DecoratedEntry (ctx := ctx),
        hit.event = .second entry)) ∨
    (∃ entry : P13ProducedPriorSupportLedger.RecordedRouteEightExtraction
        (ctx := ctx), hit.event = .third entry) := by
  cases hit.event with
  | first entry => exact .inl (.inl ⟨entry, rfl⟩)
  | second entry => exact .inl (.inr ⟨entry, rfl⟩)
  | third entry => exact .inr ⟨entry, rfl⟩

/-- Negative result after the exact full scan of the supplied produced-prior-
support ledger.  This asserts completeness only for that concrete ledger; it
does not manufacture the still-absent node-[70], [72], or [73] producers. -/
structure D6Complete (ledger : package.PriorD6Ledger)
    (stage : package.Stage) : Type (u + 1) where
  endpointOutside : ∀ key : package.D6Key ledger,
    package.currentAmbientEndpoint stage ∉
      P13ProducedPriorSupportLedger.eventSupport
        (package.d6Entry ledger key)
  projectionComplete : ∀ key : package.D6Key ledger,
    P13ProducedPriorSupportLedger.eventSupport
        (package.d6Entry ledger key) ⊆ package.boundedActiveInterface stage →
      ∃ coordinate : package.D6Coordinate ledger stage, coordinate.1 = key
  carrierCardinality : (package.boundedActiveInterface stage).card ≤ 30

abbrev D6Decision (ledger : package.PriorD6Ledger)
    (stage : package.Stage) :=
  Sum (package.D6F4Hit ledger stage) (package.D6Complete ledger stage)

/-- Local finite D6 evaluation at one stored prefix. -/
noncomputable def runD6 (ledger : package.PriorD6Ledger)
    (stage : package.Stage) : package.D6Decision ledger stage :=
  ((package.d6Profile ledger).recognize
      (package.currentAmbientEndpoint stage)).map
    (package.d6F4Hit ledger stage) fun outside => {
        endpointOutside := outside
        projectionComplete := fun key contained =>
          package.d6Coordinates_complete ledger stage key contained
        carrierCardinality := package.boundedActiveInterface_card_le_30 stage }

theorem runD6_total (ledger : package.PriorD6Ledger)
    (stage : package.Stage) :
    (∃ hit, package.runD6 ledger stage = .inl hit) ∨
      (∃ state, package.runD6 ledger stage = .inr state) := by
  cases equation : package.runD6 ledger stage with
  | inl hit => exact Or.inl ⟨hit, rfl⟩
  | inr state => exact Or.inr ⟨state, rfl⟩

theorem d6CoordinateCount_le_priorEvents
    (ledger : package.PriorD6Ledger) (stage : package.Stage) :
    (package.d6Coordinates ledger stage).card ≤
      ledger.baseState.residuals.occurrences.card :=
  (package.d6Profile ledger).activeOccurrences_card_le_occurrences
    (package.boundedActiveInterface stage)

end P13WeightedColdRestrictedPrefixPackage

end Erdos64EG.Internal
