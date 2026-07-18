import StructuralExhaustion.CT9.TokenRoleLedger
import StructuralExhaustion.Graph.InducedPathWindowLedger
import StructuralExhaustion.Graph.SurplusPairTokenRouting
import StructuralExhaustion.Graph.SurplusTokenRole

namespace StructuralExhaustion.Graph.SurplusCapacityTokenRouting

open StructuralExhaustion
open scoped Sym2

universe u

variable {input : PackedMinimumDegreeCycle.StaticInput}
variable {ctx : Core.MinimalCounterexampleContext input.problem input.Target}
variable {setup : SurplusPortActivation.Setup input ctx}
variable (stage : SurplusPortActivation.VerifiedActivatedStage input ctx setup)

abbrev Pair := SurplusPairResponse.ScheduledPair (setup := setup)
abbrev BlockedPair := SurplusPairResponse.BlockedPair stage
abbrev FreePair := SurplusPairResponse.FreePair stage
abbrev Candidate := SurplusPairBlocker.Candidate ctx.G.Vertex

/-! ## Exact three-class capacity-token universe -/

/-- Primitive carriers are exactly vertices, oriented edge incidences, and
selected surplus ports. -/
abbrev PrimitiveToken :=
  ctx.G.Vertex ⊕ ctx.G.object.graph.Dart ⊕ SurplusPortActivation.Slot setup

/-- Vertices of the selected induced-path remainder. -/
abbrev RemainderVertex :=
  {vertex : ctx.G.Vertex // vertex ∈
    InducedPathPacking.remainderVertices ctx.G.object 13 (by decide)}

/-- One degree-surplus unit at one actual remainder vertex.  The `Fin` value
is the manuscript index `j-1`. -/
abbrev RemainderToken :=
  Sigma fun vertex : RemainderVertex (ctx := ctx) =>
    Fin (ctx.G.object.degree vertex.1 - 3)

abbrev WindowToken := InducedPathWindowLedger.Token ctx.G.object

/-- Disjoint union `T_W ⊔ T_R ⊔ T_prim`. -/
abbrev Token := WindowToken (ctx := ctx) ⊕
  RemainderToken (ctx := ctx) ⊕ PrimitiveToken (ctx := ctx) (setup := setup)

@[implicit_reducible]
noncomputable def primitiveTokens :
    FinEnum (PrimitiveToken (ctx := ctx) (setup := setup)) := by
  letI : FinEnum ctx.G.Vertex := ctx.G.object.input.vertices
  letI : FinEnum ctx.G.object.graph.Dart := ctx.G.object.input.darts
  letI : FinEnum (SurplusPortActivation.Slot setup) :=
    SurplusPairResponse.slotEnumeration (setup := setup)
  exact inferInstance

@[implicit_reducible]
noncomputable def remainderVertices :
    FinEnum (RemainderVertex (ctx := ctx)) := by
  letI : FinEnum ctx.G.Vertex := ctx.G.object.input.vertices
  exact inferInstance

@[implicit_reducible]
noncomputable def remainderTokens :
    FinEnum (RemainderToken (ctx := ctx)) := by
  letI : FinEnum (RemainderVertex (ctx := ctx)) :=
    remainderVertices (ctx := ctx)
  exact inferInstance

@[implicit_reducible]
noncomputable def tokens :
    FinEnum (Token (ctx := ctx) (setup := setup)) := by
  letI : FinEnum (WindowToken (ctx := ctx)) :=
    InducedPathWindowLedger.tokens ctx.G.object
  letI : FinEnum (RemainderToken (ctx := ctx)) :=
    remainderTokens (ctx := ctx)
  letI : FinEnum (PrimitiveToken (ctx := ctx) (setup := setup)) :=
    primitiveTokens (ctx := ctx) (setup := setup)
  exact inferInstance

@[implicit_reducible]
noncomputable def pairs : FinEnum (Pair (setup := setup)) :=
  SurplusPairResponse.pairEnumeration (setup := setup)

/-- Subtype of one literal capacity token. -/
noncomputable def tokenSubtype : Token (ctx := ctx) (setup := setup) →
    SurplusTokenRole.TokenSubtype
  | .inl token => InducedPathWindowLedger.tokenSubtype ctx.G.object token
  | .inr (.inl _) => .remainderSurplus
  | .inr (.inr (.inl _)) => .primitiveVertex
  | .inr (.inr (.inr (.inl _))) => .primitiveIncidence
  | .inr (.inr (.inr (.inr _))) => .primitivePort

/-! ## Canonical blocker support and primitive carrier -/

/-- Declared edge support of an admitted blocker candidate. -/
noncomputable def supportEdges (pair : Pair (setup := setup)) :
    Candidate (ctx := ctx) → Finset (Sym2 ctx.G.Vertex)
  | .sharedSupportEdge incidence | .sharedReturnEdge incidence =>
      {incidence.edge}
  | .suppressedChordFirst =>
      {s(SurplusPortActivation.portVertex setup pair.first .leftShoulder,
        SurplusPortActivation.portVertex setup pair.first .rightShoulder)}
  | .suppressedChordSecond =>
      {s(SurplusPortActivation.portVertex setup pair.second .leftShoulder,
        SurplusPortActivation.portVertex setup pair.second .rightShoulder)}
  | _ => ∅

/-- Declared vertex support of an admitted blocker candidate. -/
noncomputable def supportVertices (pair : Pair (setup := setup)) :
    Candidate (ctx := ctx) → Finset ctx.G.Vertex := by
  classical
  intro candidate
  cases candidate with
  | sharedSupportVertex vertex | sharedReturnVertex vertex => exact {vertex}
  | sharedSupportEdge incidence | sharedReturnEdge incidence =>
      exact incidence.edge.toFinset
  | sharedPortVertex vertex _ _ => exact {vertex}
  | suppressedChordFirst =>
      exact {SurplusPortActivation.portVertex setup pair.first .leftShoulder,
        SurplusPortActivation.portVertex setup pair.first .rightShoulder}
  | suppressedChordSecond =>
      exact {SurplusPortActivation.portVertex setup pair.second .leftShoulder,
        SurplusPortActivation.portVertex setup pair.second .rightShoulder}

/-- Every actual marked graph incidence determines the unique dart directed
from its marked endpoint. -/
theorem exists_dart_of_edge_incidence
    (incidence : SurplusPairBlocker.EdgeIncidence ctx.G.Vertex)
    (actual : incidence.edge ∈ ctx.G.object.graph.edgeSet) :
    ∃ dart : ctx.G.object.graph.Dart,
      dart.edge = incidence.edge ∧ dart.fst = incidence.endpoint := by
  rcases incidence with ⟨edge, endpoint, endpointMem⟩
  dsimp only at actual endpointMem ⊢
  induction edge using Sym2.inductionOn with
  | _ left right =>
      rw [SimpleGraph.mem_edgeSet] at actual
      rw [Sym2.mem_iff] at endpointMem
      rcases endpointMem with endpointEq | endpointEq
      · subst endpoint
        exact ⟨⟨(left, right), actual⟩, rfl, rfl⟩
      · subst endpoint
        exact ⟨⟨(right, left), actual.symm⟩, Sym2.eq_swap, rfl⟩

noncomputable def dartOfEdgeIncidence
    (incidence : SurplusPairBlocker.EdgeIncidence ctx.G.Vertex)
    (actual : incidence.edge ∈ ctx.G.object.graph.edgeSet) :
    ctx.G.object.graph.Dart :=
  Classical.choose (exists_dart_of_edge_incidence (ctx := ctx) incidence actual)

theorem dartOfEdgeIncidence_edge
    (incidence : SurplusPairBlocker.EdgeIncidence ctx.G.Vertex)
    (actual : incidence.edge ∈ ctx.G.object.graph.edgeSet) :
    (dartOfEdgeIncidence (ctx := ctx) incidence actual).edge = incidence.edge :=
  (Classical.choose_spec
    (exists_dart_of_edge_incidence (ctx := ctx) incidence actual)).1

theorem dartOfEdgeIncidence_fst
    (incidence : SurplusPairBlocker.EdgeIncidence ctx.G.Vertex)
    (actual : incidence.edge ∈ ctx.G.object.graph.edgeSet) :
    (dartOfEdgeIncidence (ctx := ctx) incidence actual).fst = incidence.endpoint :=
  (Classical.choose_spec
    (exists_dart_of_edge_incidence (ctx := ctx) incidence actual)).2

/-- Primitive carrier `κ(B)` of the exact canonical first blocker. -/
noncomputable def primitiveCarrier (pair : BlockedPair stage) :
    PrimitiveToken (ctx := ctx) (setup := setup) := by
  let hit := SurplusPairResponse.canonicalBlocker stage pair
  match candidateEq : hit.value with
  | .sharedSupportVertex vertex | .sharedReturnVertex vertex =>
      exact .inl vertex
  | .sharedSupportEdge incidence =>
      have actual := pair.1.toBlockerPair.edgeCandidate_mem_edgeSet stage
        hit.value hit.member incidence (Or.inl candidateEq)
      exact .inr (.inl (dartOfEdgeIncidence (ctx := ctx) incidence actual))
  | .sharedReturnEdge incidence =>
      have actual := pair.1.toBlockerPair.edgeCandidate_mem_edgeSet stage
        hit.value hit.member incidence (Or.inr candidateEq)
      exact .inr (.inl (dartOfEdgeIncidence (ctx := ctx) incidence actual))
  | .sharedPortVertex vertex _ _ => exact .inl vertex
  | .suppressedChordFirst => exact .inr (.inr pair.1.first)
  | .suppressedChordSecond => exact .inr (.inr pair.1.second)

/-! ## Deterministic priority map -/

/-- Underlying ambient edge of one window-incidence token. -/
noncomputable def windowTokenEdge (token : WindowToken (ctx := ctx)) :
    Sym2 ctx.G.Vertex :=
  s(InducedPathWindowLedger.selectedWindow ctx.G.object token.1 token.2.1,
    token.2.2.1)

noncomputable def windowSearch (pair : BlockedPair stage) :=
  Core.FiniteSearch.first
    (InducedPathWindowLedger.tokens ctx.G.object)
    (fun token => windowTokenEdge (ctx := ctx) token ∈
      supportEdges (setup := setup) pair.1
        (SurplusPairResponse.canonicalBlocker stage pair).value)
    (fun _ => Classical.propDecidable _)

noncomputable def remainderSearch (pair : BlockedPair stage) :=
  Core.FiniteSearch.first (remainderVertices (ctx := ctx))
    (fun vertex =>
      3 < ctx.G.object.degree vertex.1 ∧
        vertex.1 ∈ supportVertices (setup := setup) pair.1
          (SurplusPairResponse.canonicalBlocker stage pair).value)
    (fun _ => Classical.propDecidable _)

/-- Canonical zero-based rank inside the pairs whose first two priority cases
fail and whose least eligible remainder vertex is `vertex`. -/
noncomputable def remainderClass (vertex : RemainderVertex (ctx := ctx)) :
    List (BlockedPair stage) := by
  letI : DecidableEq (BlockedPair stage) :=
    (SurplusPairResponse.blockedPairEnumeration stage).decEq
  letI : DecidableEq (RemainderVertex (ctx := ctx)) :=
    (remainderVertices (ctx := ctx)).decEq
  exact (SurplusPairResponse.blockedPairEnumeration stage).orderedValues.filter
    fun pair =>
      match windowSearch stage pair, remainderSearch stage pair with
      | .absent _, .found hit => decide (hit.value = vertex)
      | _, _ => false

noncomputable def remainderRank (pair : BlockedPair stage)
    (vertex : RemainderVertex (ctx := ctx)) : Nat := by
  letI : DecidableEq (BlockedPair stage) :=
    (SurplusPairResponse.blockedPairEnumeration stage).decEq
  exact (remainderClass stage vertex).idxOf pair

noncomputable def selectedRemainderToken (pair : BlockedPair stage)
    (hit : Core.FiniteSearch.FirstHit
      (remainderVertices (ctx := ctx)).orderedValues
      (fun vertex => 3 < ctx.G.object.degree vertex.1 ∧
        vertex.1 ∈ supportVertices (setup := setup) pair.1
          (SurplusPairResponse.canonicalBlocker stage pair).value)) :
    RemainderToken (ctx := ctx) :=
  ⟨hit.value,
    ⟨remainderRank stage pair hit.value %
        (ctx.G.object.degree hit.value.1 - 3),
      Nat.mod_lt _ (Nat.sub_pos_of_lt hit.holds.1)⟩⟩

/-- Exact capacity-token priority `(a)`--`(d)` for one blocked pair. -/
noncomputable def blockedToken (pair : BlockedPair stage) :
    Token (ctx := ctx) (setup := setup) :=
  match windowSearch stage pair with
  | .found hit => .inl hit.value
  | .absent _ =>
      match remainderSearch stage pair with
      | .found hit => .inr (.inl (selectedRemainderToken stage pair hit))
      | .absent _ => .inr (.inr (primitiveCarrier stage pair))

/-- Complete map on the original pair schedule.  Free pairs use their literal
first selected port; blocked pairs use the capacity priority above. -/
noncomputable def pairToken (pair : Pair (setup := setup)) :
    Token (ctx := ctx) (setup := setup) :=
  match (SurplusPairResponse.blockerFamily stage).hasBlockerDecidable pair with
  | .isTrue blocked => blockedToken stage ⟨pair, blocked⟩
  | .isFalse _ => .inr (.inr (.inr (.inr pair.first)))

noncomputable def pairRole (pair : Pair (setup := setup)) :
    SurplusTokenRole.TotalRole :=
  match (SurplusPairResponse.blockerFamily stage).hasBlockerDecidable pair with
  | .isTrue blocked =>
      let blockedPair : BlockedPair stage := ⟨pair, blocked⟩
      let candidate := (SurplusPairResponse.canonicalBlocker stage blockedPair).value
      .blocked (SurplusTokenRole.admittedKind candidate,
        tokenSubtype (ctx := ctx) (setup := setup) (blockedToken stage blockedPair))
  | .isFalse _ => .freeAnchor

/-! ## Exact CT9 relabelling and local accounting -/

/-- The capacity labels refine the already executed CT9 pair ledger from node
`[130]`.  The item collection is unchanged; only its total label map is
refined to the manuscript's capacity-token/role product. -/

noncomputable def capability : CT9.Capability input.problem :=
  CT9.TokenRoleLedger.capability input.problem (Pair (setup := setup))
    (tokens (ctx := ctx) (setup := setup)) SurplusTokenRole.totalRoleEnum
    (pairToken stage) (pairRole stage)

noncomputable def ct9Input : CT9.Input (capability stage) :=
  CT9.TokenRoleLedger.input (capacity := fun _ _ => 0)
    ctx.toBranchContext (pairs (setup := setup)).toOrderedCollection

/-- Node `[136]`: the 25 token--role fibres partition the complete pair
schedule exactly once. -/
theorem noOvercounting :
    (ct9Input stage).items.values.length =
      ((capability stage).labels.orderedValues.map fun labelValue =>
        CT9.fibreCount (capability stage) (ct9Input stage) labelValue).sum :=
  CT9.cardinality_eq_sum_fibreCount (capability stage) (ct9Input stage)

/-- The refined CT9 ledger consumes exactly the same complete pair schedule
as the already verified source execution. -/
theorem input_items_eq_source :
    (ct9Input stage).items =
      (SurplusPairTokenRouting.ct9Input stage).items := rfl

theorem free_role (pair : FreePair stage) :
    pairRole stage pair.1 = .freeAnchor := by
  unfold pairRole
  cases decision :
      (SurplusPairResponse.blockerFamily stage).hasBlockerDecidable pair.1 with
  | isTrue blocked => exact (pair.2 blocked).elim
  | isFalse _ => rfl

theorem free_token (pair : FreePair stage) :
    pairToken stage pair.1 = .inr (.inr (.inr (.inr pair.1.first))) := by
  unfold pairToken
  cases decision :
      (SurplusPairResponse.blockerFamily stage).hasBlockerDecidable pair.1 with
  | isTrue blocked => exact (pair.2 blocked).elim
  | isFalse _ => rfl

theorem blocked_token (pair : BlockedPair stage) :
    pairToken stage pair.1 = blockedToken stage pair := by
  unfold pairToken
  cases decision :
      (SurplusPairResponse.blockerFamily stage).hasBlockerDecidable pair.1 with
  | isTrue _ => rfl
  | isFalse notBlocked => exact (notBlocked pair.2).elim

/-! ## Original blocked-pair ledger

The manuscript's node `[136]` partitions only the positive blocker branch.
The complete-pair ledger below is useful for later bookkeeping, but it does
not replace this exact predecessor-indexed CT9 execution. -/

@[implicit_reducible]
noncomputable def blockedPairs : FinEnum (BlockedPair stage) :=
  SurplusPairResponse.blockedPairEnumeration stage

noncomputable def blockedRole (pair : BlockedPair stage) :
    SurplusTokenRole.AdmittedRole :=
  (SurplusTokenRole.admittedKind
      (SurplusPairResponse.canonicalBlocker stage pair).value,
    tokenSubtype (ctx := ctx) (setup := setup) (blockedToken stage pair))

noncomputable def blockedCapability : CT9.Capability input.problem :=
  CT9.TokenRoleLedger.capability input.problem (BlockedPair stage)
    (tokens (ctx := ctx) (setup := setup)) SurplusTokenRole.admittedRoleEnum
    (blockedToken stage) (blockedRole stage)

noncomputable def blockedInput : CT9.Input (blockedCapability stage) :=
  CT9.TokenRoleLedger.input (capacity := fun _ _ => 0)
    ctx.toBranchContext (blockedPairs stage).toOrderedCollection

noncomputable def blockedRun :=
  CT9.TokenRoleLedger.run
    (tokens (ctx := ctx) (setup := setup)) SurplusTokenRole.admittedRoleEnum
    (blockedToken stage) (blockedRole stage) ctx.toBranchContext
    (blockedPairs stage).toOrderedCollection

/-- Exact original node-`[136]` identity: every admitted blocked pair occurs
in one and only one capacity-token/admitted-role fibre. -/
theorem blocked_noOvercounting :
    (blockedInput stage).items.values.length =
      ((blockedCapability stage).labels.orderedValues.map fun labelValue =>
        CT9.fibreCount (blockedCapability stage) (blockedInput stage)
          labelValue).sum :=
  CT9.TokenRoleLedger.noOvercounting
    (tokens (ctx := ctx) (setup := setup)) SurplusTokenRole.admittedRoleEnum
    (blockedToken stage) (blockedRole stage) ctx.toBranchContext
    (blockedPairs stage).toOrderedCollection

theorem blocked_role_card : SurplusTokenRole.admittedRoleEnum.card = 24 :=
  SurplusTokenRole.admittedRole_card

noncomputable def blockedChecks : Nat :=
  CT9.TokenRoleLedger.checks
    (tokens (ctx := ctx) (setup := setup)) SurplusTokenRole.admittedRoleEnum
    (blockedPairs stage).toOrderedCollection

theorem blockedChecks_eq :
    blockedChecks stage = (blockedPairs stage).card *
      ((tokens (ctx := ctx) (setup := setup)).card * 24) := by
  rw [blockedChecks, CT9.TokenRoleLedger.checks_enumeration_eq,
    SurplusTokenRole.admittedRole_card]

/-- Complete CT9 execution certificate for the original blocked-pair branch.
Only the already produced blocked subtype is scanned. -/
noncomputable def blockedVerifiedStage :
    CT9.TokenRoleLedger.VerifiedStage
      (tokens (ctx := ctx) (setup := setup))
      SurplusTokenRole.admittedRoleEnum (blockedToken stage)
      (blockedRole stage) ctx.toBranchContext
      (blockedPairs stage).toOrderedCollection :=
  CT9.TokenRoleLedger.verifiedStage
    (tokens (ctx := ctx) (setup := setup)) SurplusTokenRole.admittedRoleEnum
    (blockedToken stage) (blockedRole stage) ctx.toBranchContext
    (blockedPairs stage).toOrderedCollection

/-- Original manuscript role, including the two raw audit kinds.  The local
candidate theorem proves that those twelve product rows are empty, but keeping
them in the label universe gives the literal `Q_st = 36` accounting. -/
noncomputable def blockedFullRole (pair : BlockedPair stage) :
    SurplusTokenRole.Role :=
  ((SurplusPairResponse.canonicalBlocker stage pair).value.kind,
    tokenSubtype (ctx := ctx) (setup := setup) (blockedToken stage pair))

theorem blockedFullRole_kind_ne_audit (pair : BlockedPair stage) :
    (blockedFullRole stage pair).1 ≠ .profile ∧
      (blockedFullRole stage pair).1 ≠ .target := by
  exact SurplusPairBlocker.Pair.candidate_kind_ne_profile_target
    (SurplusPairResponse.canonicalBlocker stage pair).value

noncomputable def blockedFullCapability : CT9.Capability input.problem :=
  CT9.TokenRoleLedger.capability input.problem (BlockedPair stage)
    (tokens (ctx := ctx) (setup := setup)) SurplusTokenRole.roleEnum
    (blockedToken stage) (blockedFullRole stage)

noncomputable def blockedFullInput : CT9.Input (blockedFullCapability stage) :=
  CT9.TokenRoleLedger.input (capacity := fun _ _ => 0)
    ctx.toBranchContext (blockedPairs stage).toOrderedCollection

theorem blockedFull_noOvercounting :
    (blockedFullInput stage).items.values.length =
      ((blockedFullCapability stage).labels.orderedValues.map fun labelValue =>
        CT9.fibreCount (blockedFullCapability stage) (blockedFullInput stage)
          labelValue).sum :=
  CT9.TokenRoleLedger.noOvercounting
    (tokens (ctx := ctx) (setup := setup)) SurplusTokenRole.roleEnum
    (blockedToken stage) (blockedFullRole stage) ctx.toBranchContext
    (blockedPairs stage).toOrderedCollection

theorem blocked_full_role_card : SurplusTokenRole.roleEnum.card = 36 :=
  SurplusTokenRole.role_card

noncomputable def blockedFullVerifiedStage :
    CT9.TokenRoleLedger.VerifiedStage
      (tokens (ctx := ctx) (setup := setup)) SurplusTokenRole.roleEnum
      (blockedToken stage) (blockedFullRole stage) ctx.toBranchContext
      (blockedPairs stage).toOrderedCollection :=
  CT9.TokenRoleLedger.verifiedStage
    (tokens (ctx := ctx) (setup := setup)) SurplusTokenRole.roleEnum
    (blockedToken stage) (blockedFullRole stage) ctx.toBranchContext
    (blockedPairs stage).toOrderedCollection

theorem role_card : SurplusTokenRole.totalRoleEnum.card = 25 :=
  SurplusTokenRole.totalRole_card

theorem primitive_card :
    (primitiveTokens (ctx := ctx) (setup := setup)).card =
      ctx.G.object.input.vertices.card +
        (ctx.G.object.input.darts).card +
        (SurplusPairResponse.slotEnumeration (setup := setup)).card := by
  letI : FinEnum ctx.G.Vertex := ctx.G.object.input.vertices
  letI : FinEnum ctx.G.object.graph.Dart := ctx.G.object.input.darts
  letI : FinEnum (SurplusPortActivation.Slot setup) :=
    SurplusPairResponse.slotEnumeration (setup := setup)
  simp [FinEnum.card_eq_fintypeCard, Nat.add_assoc]

theorem remainder_card :
    (remainderTokens (ctx := ctx)).card =
      ∑ vertex : RemainderVertex (ctx := ctx),
        (ctx.G.object.degree vertex.1 - 3) := by
  letI : FinEnum (RemainderVertex (ctx := ctx)) :=
    remainderVertices (ctx := ctx)
  rw [FinEnum.card_eq_fintypeCard]
  simp [Fintype.card_sigma]

theorem remainder_card_eq_remainderSurplus :
    (remainderTokens (ctx := ctx)).card =
      InducedPathWindowLedger.remainderSurplus ctx.G.object := by
  rw [remainder_card]
  letI : FinEnum ctx.G.Vertex := ctx.G.object.input.vertices
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  letI : Fintype (RemainderVertex (ctx := ctx)) :=
    @FinEnum.instFintype _ (remainderVertices (ctx := ctx))
  unfold InducedPathWindowLedger.remainderSurplus RemainderVertex
  symm
  exact Finset.sum_subtype
    (InducedPathPacking.remainderVertices ctx.G.object 13 (by decide))
    (fun _ => Iff.rfl) (fun vertex => ctx.G.object.degree vertex - 3)

theorem darts_card_eq_twice_edges :
    (ctx.G.object.input.darts).card = 2 * ctx.G.object.edgeCount := by
  letI : FinEnum ctx.G.Vertex := ctx.G.object.input.vertices
  letI : FinEnum ctx.G.object.graph.Dart := ctx.G.object.input.darts
  letI : DecidableRel ctx.G.object.graph.Adj := ctx.G.object.input.decideAdj
  rw [FinEnum.card_eq_fintypeCard]
  exact ctx.G.object.graph.dart_card_eq_twice_card_edges

theorem primitive_card_eq_vertex_edges_surplus :
    (primitiveTokens (ctx := ctx) (setup := setup)).card =
      ctx.G.object.input.vertices.card + 2 * ctx.G.object.edgeCount +
        InducedPathWindowLedger.totalSurplus ctx.G.object := by
  rw [primitive_card, darts_card_eq_twice_edges]
  rw [SurplusPortActivity.portSlots_card_eq_surplus]
  rfl

theorem token_supply_exact :
    (tokens (ctx := ctx) (setup := setup)).card =
      (InducedPathWindowLedger.tokens ctx.G.object).card +
        (remainderTokens (ctx := ctx)).card +
        (primitiveTokens (ctx := ctx) (setup := setup)).card := by
  letI : FinEnum (WindowToken (ctx := ctx)) :=
    InducedPathWindowLedger.tokens ctx.G.object
  letI : FinEnum (RemainderToken (ctx := ctx)) :=
    remainderTokens (ctx := ctx)
  letI : FinEnum (PrimitiveToken (ctx := ctx) (setup := setup)) :=
    primitiveTokens (ctx := ctx) (setup := setup)
  simp [FinEnum.card_eq_fintypeCard, Nat.add_assoc]

/-- Fully simplified exact supply identity from the manuscript. -/
theorem token_supply_exact_simplified
    (baseline : ∀ vertex, 3 ≤ ctx.G.object.degree vertex) :
    (tokens (ctx := ctx) (setup := setup)).card =
      (ctx.G.object.input.vertices.card + 2 * ctx.G.object.edgeCount +
        InducedPathWindowLedger.totalSurplus ctx.G.object) +
      15 * InducedPathWindowLedger.packingNumber ctx.G.object +
        InducedPathWindowLedger.totalSurplus ctx.G.object := by
  rw [token_supply_exact, primitive_card_eq_vertex_edges_surplus,
    remainder_card_eq_remainderSurplus,
    InducedPathWindowLedger.tokens_card_eq_fifteen_mul_packing_add_surplus
      ctx.G.object baseline]
  have partition :=
    InducedPathWindowLedger.window_add_remainder_eq_totalSurplus ctx.G.object
  omega

/-- Exact local work count for the CT9 product scan. -/
noncomputable def checks
    (_stage : SurplusPortActivation.VerifiedActivatedStage input ctx setup) : Nat :=
  CT9.TokenRoleLedger.checks
    (tokens (ctx := ctx) (setup := setup)) SurplusTokenRole.totalRoleEnum
    (pairs (setup := setup)).toOrderedCollection

theorem checks_eq : checks stage = (pairs (setup := setup)).card *
    ((tokens (ctx := ctx) (setup := setup)).card * 25) := by
  unfold checks
  rw [CT9.TokenRoleLedger.checks_enumeration_eq,
    SurplusTokenRole.totalRole_card]

/-- Complete reusable certificate for nodes `[134]`--`[136]`. -/
structure VerifiedStage : Prop where
  source : SurplusPairTokenRouting.VerifiedStage stage
  exactInput : (ct9Input stage).items =
    (SurplusPairTokenRouting.ct9Input stage).items
  exactLedger : (ct9Input stage).items.values.length =
    ((capability stage).labels.orderedValues.map fun labelValue =>
      CT9.fibreCount (capability stage) (ct9Input stage) labelValue).sum
  freeRoute : ∀ pair : FreePair stage,
    pairToken stage pair.1 = .inr (.inr (.inr (.inr pair.1.first))) ∧
      pairRole stage pair.1 = .freeAnchor
  blockedRoute : ∀ pair : BlockedPair stage,
    pairToken stage pair.1 = blockedToken stage pair
  roleCount : SurplusTokenRole.totalRoleEnum.card = 25
  supply : (tokens (ctx := ctx) (setup := setup)).card =
    (InducedPathWindowLedger.tokens ctx.G.object).card +
      (remainderTokens (ctx := ctx)).card +
      (primitiveTokens (ctx := ctx) (setup := setup)).card
  checkCount : checks stage = (pairs (setup := setup)).card *
    ((tokens (ctx := ctx) (setup := setup)).card * 25)

noncomputable def verifiedStage : VerifiedStage stage where
  source := SurplusPairTokenRouting.verifiedStage stage
  exactInput := input_items_eq_source stage
  exactLedger := noOvercounting stage
  freeRoute := fun pair => ⟨free_token stage pair, free_role stage pair⟩
  blockedRoute := blocked_token stage
  roleCount := role_card
  supply := token_supply_exact
  checkCount := checks_eq stage

end StructuralExhaustion.Graph.SurplusCapacityTokenRouting
