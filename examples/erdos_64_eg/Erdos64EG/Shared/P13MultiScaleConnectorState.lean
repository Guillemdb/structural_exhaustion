import Erdos64EG.Node21
import StructuralExhaustion.Core.FiniteSearch
import StructuralExhaustion.Graph.InducedPathConnectorCycle
import Mathlib.Tactic

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-!
# Graph-owned connector states for the 91 P13 barriers

For one literal CT12-selected window and one node-[21] barrier index, a raw
candidate is a fifteen-slot ambient vertex sequence.  Only the prefix through
`a+b` is active.  The executable predicate below requires that prefix to be a
simple path outside the window, with the declared source/middle/target slots,
legal actual attachment labels, and the two node-[21] local-safe relations.

This constructs an actual finite graph-owned state universe.  It does not
assert that a state exists, does not insert arbitrary label triples, and does
not claim that independently selected connector paths commute as graph
modifications.  The first absent local connector is retained as a typed
residual.
-/

/-- Fifteen slots suffice because every accepted barrier has `a+b <= 14`. -/
abbrev P13ConnectorSequence
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  Fin 15 → ctx.G.Vertex

/-- One literal member of the exact CT12-selected packing. -/
abbrev P13SelectedConnectorWindow
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  {window : InducedP13Window ctx // window ∈ p13Windows ctx}

@[implicit_reducible]
noncomputable def p13ConnectorSequences
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    FinEnum (P13ConnectorSequence ctx) := by
  letI : FinEnum ctx.G.Vertex := ctx.G.object.input.vertices
  infer_instance

theorem p13ConnectorSequences_card
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    (p13ConnectorSequences ctx).card =
      ctx.G.object.input.vertices.card ^ 15 := by
  letI : FinEnum ctx.G.Vertex := ctx.G.object.input.vertices
  letI : Fintype ctx.G.Vertex := inferInstance
  rw [FinEnum.card_eq_fintypeCard, Fintype.card_fun,
    ← FinEnum.card_eq_fintypeCard]
  simp

/-- One pass through all 91 barriers and all bounded connector sequences.
The exponent 15 is fixed by the local P13 interface; no graph family or
unbounded walk universe is enumerated. -/
def p13BarrierConnectorCheckBudget
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Nat :=
  91 * ctx.G.object.input.vertices.card ^ 15

def p13BarrierLeftSlot (index : P13BarrierIndex) : Fin 15 :=
  ⟨index.leftLength, (p13BarrierIndex_lt_fifteen index).1⟩

def p13BarrierTotalSlot (index : P13BarrierIndex) : Fin 15 :=
  ⟨index.leftLength + index.rightLength, by
    exact lt_of_le_of_lt (p13BarrierIndex_sum_le_fourteen index) (by decide)⟩

def p13SequenceOutside
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (window : P13SelectedConnectorWindow ctx) (total : Nat)
    (sequence : P13ConnectorSequence ctx) : Prop :=
  ∀ slot : Fin 15, slot.1 ≤ total →
    ∀ position : Fin 13, sequence slot ≠ window.1 position

def p13SequenceSimplePrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (total : Nat) (sequence : P13ConnectorSequence ctx) : Prop :=
  ∀ left right : Fin 15,
    left.1 ≤ total → right.1 ≤ total →
      sequence left = sequence right → left = right

def p13SequenceAdjacentPrefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (total : Nat) (sequence : P13ConnectorSequence ctx) : Prop :=
  ∀ slot : Fin 14, slot.1 < total →
    ctx.G.object.graph.Adj
      (sequence ⟨slot.1, by omega⟩)
      (sequence ⟨slot.1 + 1, by omega⟩)

def p13SequenceLabel
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (window : P13SelectedConnectorWindow ctx) (sequence : P13ConnectorSequence ctx)
    (slot : Fin 15) : P13Label :=
  packedStaticInput.inducedPathAttachmentLabel 13 ctx window.1 (sequence slot)

/-- Exact executable validity predicate for one graph-owned two-step
connector.  Every clause is computed from the selected graph, selected
window, barrier index, and candidate sequence. -/
def P13BarrierConnectorValid
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (window : P13SelectedConnectorWindow ctx) (index : P13BarrierIndex)
    (sequence : P13ConnectorSequence ctx) : Prop :=
  let source := p13SequenceLabel ctx window sequence ⟨0, by decide⟩
  let middle := p13SequenceLabel ctx window sequence
    (p13BarrierLeftSlot index)
  let target := p13SequenceLabel ctx window sequence
    (p13BarrierTotalSlot index)
  p13SequenceOutside ctx window
      (index.leftLength + index.rightLength) sequence ∧
    p13SequenceSimplePrefix ctx
      (index.leftLength + index.rightLength) sequence ∧
    p13SequenceAdjacentPrefix ctx
      (index.leftLength + index.rightLength) sequence ∧
    p13CodeLegalBool (encodeP13Label source) = true ∧
    p13CodeLegalBool (encodeP13Label middle) = true ∧
    p13CodeLegalBool (encodeP13Label target) = true ∧
    p13C index.leftLength source middle = 1 ∧
    p13C index.rightLength middle target = 1

def p13BarrierConnectorValidDecidable
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (window : P13SelectedConnectorWindow ctx) (index : P13BarrierIndex)
    (sequence : P13ConnectorSequence ctx) :
    Decidable (P13BarrierConnectorValid ctx window index sequence) := by
  letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
  letI : DecidableRel ctx.G.object.graph.Adj :=
    ctx.G.object.input.decideAdj
  letI : DecidablePred PowerOfTwoLength := powerOfTwoLengthDecidable
  unfold P13BarrierConnectorValid p13SequenceOutside
    p13SequenceSimplePrefix p13SequenceAdjacentPrefix
  infer_instance

theorem p13CodeLegalBool_encode_eq_true_iff (label : P13Label) :
    p13CodeLegalBool (encodeP13Label label) = true ↔ P13Legal label := by
  have encoded : p13LabelEquiv (encodeP13Label label) = label := by
    exact p13LabelEquiv.apply_symm_apply label
  constructor
  · intro accepted
    have codeLegal : P13CodeLegal (encodeP13Label label) := by
      simpa [p13CodeLegalBool, P13LabelKernel.codeLegalBool] using accepted
    have gapEncoded :=
      (p13CodeLegal_iff_gapLegal (encodeP13Label label)).1 codeLegal
    have gap : P13GapLegal label := by simpa [encoded] using gapEncoded
    exact (p13Legal_iff_gapLegal label).2 gap
  · intro legal
    have gap : P13GapLegal label := (p13Legal_iff_gapLegal label).1 legal
    have gapEncoded : P13GapLegal
        (p13LabelEquiv (encodeP13Label label)) := by simpa [encoded] using gap
    have codeLegal :=
      (p13CodeLegal_iff_gapLegal (encodeP13Label label)).2 gapEncoded
    simpa [p13CodeLegalBool, P13LabelKernel.codeLegalBool] using codeLegal

/-- Actual safe connector states for one barrier. -/
abbrev P13BarrierConnectorState
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (window : P13SelectedConnectorWindow ctx) (index : P13BarrierIndex) :=
  {sequence : P13ConnectorSequence ctx //
    P13BarrierConnectorValid ctx window index sequence}

@[implicit_reducible]
noncomputable def p13BarrierConnectorStates
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (window : P13SelectedConnectorWindow ctx) (index : P13BarrierIndex) :
    FinEnum (P13BarrierConnectorState ctx window index) := by
  letI : FinEnum (P13ConnectorSequence ctx) := p13ConnectorSequences ctx
  letI : DecidablePred (P13BarrierConnectorValid ctx window index) :=
    p13BarrierConnectorValidDecidable ctx window index
  infer_instance

/-- The flat bit of an actual locally-safe connector.  This is precisely the
third relation used by node [21], now evaluated on actual attachment labels. -/
def p13BarrierConnectorFlat
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (window : P13SelectedConnectorWindow ctx) (index : P13BarrierIndex)
    (state : P13BarrierConnectorState ctx window index) : Bool :=
  decide <| p13C (index.leftLength + index.rightLength)
    (p13SequenceLabel ctx window state.1 ⟨0, by decide⟩)
    (p13SequenceLabel ctx window state.1 (p13BarrierTotalSlot index)) = 1

theorem p13BarrierConnectorFlat_eq_true_iff
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (window : P13SelectedConnectorWindow ctx) (index : P13BarrierIndex)
    (state : P13BarrierConnectorState ctx window index) :
    p13BarrierConnectorFlat ctx window index state = true ↔
      p13C (index.leftLength + index.rightLength)
        (p13SequenceLabel ctx window state.1 ⟨0, by decide⟩)
        (p13SequenceLabel ctx window state.1
          (p13BarrierTotalSlot index)) = 1 := by
  simp [p13BarrierConnectorFlat]

/-- Every retained connector state lies in exactly the safe-triple domain
whose flat subfamily was counted at node [21]. -/
theorem p13BarrierConnectorState_safe_semantics
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (window : P13SelectedConnectorWindow ctx) (index : P13BarrierIndex)
    (state : P13BarrierConnectorState ctx window index) :
    let source := p13SequenceLabel ctx window state.1 ⟨0, by decide⟩
    let middle := p13SequenceLabel ctx window state.1
      (p13BarrierLeftSlot index)
    let target := p13SequenceLabel ctx window state.1
      (p13BarrierTotalSlot index)
    P13Legal source ∧ P13Legal middle ∧ P13Legal target ∧
      p13C index.leftLength source middle = 1 ∧
      p13C index.rightLength middle target = 1 := by
  rcases state.property with
    ⟨_outside, _simple, _adjacent, sourceLegal, middleLegal, targetLegal,
      leftSafe, rightSafe⟩
  exact ⟨(p13CodeLegalBool_encode_eq_true_iff _).1 sourceLegal,
    (p13CodeLegalBool_encode_eq_true_iff _).1 middleLegal,
    (p13CodeLegalBool_encode_eq_true_iff _).1 targetLegal,
    leftSafe, rightSafe⟩

private def p13SequenceWalk
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (sequence : P13ConnectorSequence ctx) :
    (length : Nat) → (length_lt : length < 15) →
      p13SequenceAdjacentPrefix ctx length sequence →
      ctx.G.object.graph.Walk (sequence ⟨0, by decide⟩)
        (sequence ⟨length, length_lt⟩)
  | 0, _length_lt, _adjacent => .nil
  | length + 1, length_lt, adjacent =>
      (p13SequenceWalk ctx sequence length (by omega) (by
        intro slot slot_lt
        exact adjacent slot (lt_trans slot_lt (Nat.lt_succ_self length)))).concat
          (adjacent ⟨length, by omega⟩ (by
            show length < length + 1
            omega))

private theorem p13SequenceWalk_length
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (sequence : P13ConnectorSequence ctx) (length : Nat)
    (length_lt : length < 15)
    (adjacent : p13SequenceAdjacentPrefix ctx length sequence) :
    (p13SequenceWalk ctx sequence length length_lt adjacent).length = length := by
  induction length with
  | zero => rfl
  | succ length ih =>
      simp only [p13SequenceWalk, SimpleGraph.Walk.length_concat]
      have previous := ih (by omega) (by
        intro slot slot_lt
        exact adjacent slot (lt_trans slot_lt (Nat.lt_succ_self length)))
      omega

private theorem p13SequenceWalk_support_slot
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (sequence : P13ConnectorSequence ctx) (length : Nat)
    (length_lt : length < 15)
    (adjacent : p13SequenceAdjacentPrefix ctx length sequence)
    (vertex : ctx.G.Vertex)
    (member : vertex ∈
      (p13SequenceWalk ctx sequence length length_lt adjacent).support) :
    ∃ slot : Fin 15, slot.1 ≤ length ∧ vertex = sequence slot := by
  induction length with
  | zero =>
      simp only [p13SequenceWalk, SimpleGraph.Walk.support_nil,
        List.mem_singleton] at member
      exact ⟨⟨0, by decide⟩, Nat.zero_le 0, member⟩
  | succ length ih =>
      simp only [p13SequenceWalk, SimpleGraph.Walk.support_concat,
        List.mem_append, List.mem_singleton] at member
      rcases member with member | equal
      · obtain ⟨slot, slot_le, value⟩ := ih (by omega) (by
          intro index index_lt
          exact adjacent index
            (lt_trans index_lt (Nat.lt_succ_self length))) member
        exact ⟨slot, slot_le.trans (Nat.le_succ length), value⟩
      · exact ⟨⟨length + 1, length_lt⟩, Nat.le_refl _, equal⟩

private theorem p13SequenceWalk_isPath
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (sequence : P13ConnectorSequence ctx) (length : Nat)
    (length_lt : length < 15)
    (adjacent : p13SequenceAdjacentPrefix ctx length sequence)
    (simple : p13SequenceSimplePrefix ctx length sequence) :
    (p13SequenceWalk ctx sequence length length_lt adjacent).IsPath := by
  induction length with
  | zero => simp [p13SequenceWalk]
  | succ length ih =>
      let previousAdjacent : p13SequenceAdjacentPrefix ctx length sequence := by
        intro slot slot_lt
        exact adjacent slot (lt_trans slot_lt (Nat.lt_succ_self length))
      have previousSimple : p13SequenceSimplePrefix ctx length sequence := by
        intro left right left_le right_le equal
        exact simple left right (left_le.trans (Nat.le_succ length))
          (right_le.trans (Nat.le_succ length)) equal
      apply (ih (by omega) previousAdjacent previousSimple).concat
      intro member
      obtain ⟨slot, slot_le, equal⟩ :=
        p13SequenceWalk_support_slot ctx sequence length (by omega)
          previousAdjacent _ member
      have slotsEqual := simple ⟨length + 1, length_lt⟩ slot
        (Nat.le_refl _) (slot_le.trans (Nat.le_succ length)) equal
      have valuesEqual := congrArg Fin.val slotsEqual
      simp at valuesEqual
      omega

/-- Actual connector paths in the fixed target-avoiding graph are always in
the composition-flat subfamily.  Therefore they cannot realize the false
bits required by a complete Boolean cube; those bits would have to come from
hypothetical graph completions, not from paths already present in `ctx.G`. -/
theorem p13BarrierConnectorFlat_true
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (window : P13SelectedConnectorWindow ctx) (index : P13BarrierIndex)
    (state : P13BarrierConnectorState ctx window index) :
    p13BarrierConnectorFlat ctx window index state = true := by
  rw [p13BarrierConnectorFlat_eq_true_iff, p13C_eq_one_iff]
  intro leftPosition leftMember rightPosition rightMember targetLength
  rcases state.property with
    ⟨outside, simple, adjacent, _sourceLegal, _middleLegal, _targetLegal,
      _leftSafe, _rightSafe⟩
  let total := index.leftLength + index.rightLength
  have total_lt : total < 15 := by
    exact lt_of_le_of_lt (p13BarrierIndex_sum_le_fourteen index) (by decide)
  let connector := p13SequenceWalk ctx state.1 total total_lt adjacent
  have connectorPath : connector.IsPath :=
    p13SequenceWalk_isPath ctx state.1 total total_lt adjacent simple
  have connectorOutside : ∀ vertex ∈ connector.support,
      ∀ position : Fin 13, vertex ≠ window.1 position := by
    intro vertex member position equal
    obtain ⟨slot, slot_le, vertexEq⟩ :=
      p13SequenceWalk_support_slot ctx state.1 total total_lt adjacent
        vertex member
    exact outside slot slot_le position (vertexEq.symm.trans equal)
  have total_pos : 0 < total := by
    have positive := p13BarrierIndex_positive index
    omega
  have outsideDistinct : state.1 ⟨0, by decide⟩ ≠
      state.1 (p13BarrierTotalSlot index) := by
    intro equal
    have slotsEqual := simple ⟨0, by decide⟩
      (p13BarrierTotalSlot index) (Nat.zero_le _)
      (Nat.le_refl _) equal
    have valuesEqual := congrArg Fin.val slotsEqual
    simp [p13BarrierTotalSlot] at valuesEqual
    omega
  letI : DecidableRel ctx.G.object.graph.Adj :=
    ctx.G.object.input.decideAdj
  have leftAdjacent : ctx.G.object.graph.Adj
      (state.1 ⟨0, by decide⟩) (window.1 leftPosition) :=
    (Graph.InducedPathAttachment.mem_attachmentLabel_iff
      window.1 (state.1 ⟨0, by decide⟩) leftPosition).1 leftMember
  have rightAdjacent : ctx.G.object.graph.Adj
      (state.1 (p13BarrierTotalSlot index)) (window.1 rightPosition) :=
    (Graph.InducedPathAttachment.mem_attachmentLabel_iff
      window.1 (state.1 (p13BarrierTotalSlot index)) rightPosition).1
        rightMember
  have cycle := Graph.InducedPathConnectorCycle.connectorCycle
    PowerOfTwoLength window.1 connector connectorPath connectorOutside
      outsideDistinct leftPosition rightPosition leftAdjacent rightAdjacent
      (by
        rw [p13SequenceWalk_length]
        simpa [total, Graph.InducedPathAttachment.crossCycleLength,
          Nat.add_assoc] using targetLength)
  exact ctx.avoids ⟨cycle⟩

/-- A canonical local residual: this specific audited barrier has no actual
safe connector sequence in the selected graph around the selected window. -/
structure P13MissingBarrierConnector
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (window : P13SelectedConnectorWindow ctx) where
  index : P13BarrierIndex
  absent : ∀ sequence : P13ConnectorSequence ctx,
    ¬P13BarrierConnectorValid ctx window index sequence

/-- Positive side of the both-sides test: every one of the 91 audited
barriers has at least one literal locally-safe outside connector. -/
def P13AllBarrierConnectorsPresent
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (window : P13SelectedConnectorWindow ctx) : Prop :=
  ∀ index : P13BarrierIndex,
    ∃ sequence, P13BarrierConnectorValid ctx window index sequence

noncomputable def p13BarrierConnectorSearch
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (window : P13SelectedConnectorWindow ctx) (index : P13BarrierIndex) :=
  Core.FiniteSearch.search (p13ConnectorSequences ctx)
    (P13BarrierConnectorValid ctx window index)
    (p13BarrierConnectorValidDecidable ctx window index)

noncomputable def p13BarrierMissingDecidable
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (window : P13SelectedConnectorWindow ctx) (index : P13BarrierIndex) :
    Decidable (∀ sequence, ¬P13BarrierConnectorValid ctx window index sequence) :=
  match p13BarrierConnectorSearch ctx window index with
  | .found sequence valid => isFalse fun absent => absent sequence valid
  | .absent absent => isTrue absent

noncomputable def p13FirstMissingBarrierConnector
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (window : P13SelectedConnectorWindow ctx) :=
  Core.FiniteSearch.first
    p13BarrierClassification.classes
    (fun index => ∀ sequence,
      ¬P13BarrierConnectorValid ctx window index sequence)
    (p13BarrierMissingDecidable ctx window)

/-- Executable exhaustive local outcome.  It does not request connector
nonemptiness from the caller. -/
inductive P13BarrierConnectorOutcome
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (window : P13SelectedConnectorWindow ctx)
  | complete (present : P13AllBarrierConnectorsPresent ctx window)
  | missing (residual : P13MissingBarrierConnector ctx window)

noncomputable def classifyP13BarrierConnectors
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (window : P13SelectedConnectorWindow ctx) :
    P13BarrierConnectorOutcome ctx window := by
  cases result : p13FirstMissingBarrierConnector ctx window with
  | found hit => exact .missing ⟨hit.value, hit.holds⟩
  | absent none =>
      apply P13BarrierConnectorOutcome.complete
      intro index
      cases found : p13BarrierConnectorSearch ctx window index with
      | found sequence valid => exact ⟨sequence, valid⟩
      | absent absent =>
          have missing : ∀ sequence,
              ¬P13BarrierConnectorValid ctx window index sequence := absent
          exact (none index
            (p13BarrierClassification.classes.mem_orderedValues index)
            missing).elim

theorem classifyP13BarrierConnectors_total
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (window : P13SelectedConnectorWindow ctx) :
    match classifyP13BarrierConnectors ctx window with
    | .complete present => P13AllBarrierConnectorsPresent ctx window
    | .missing residual => ∀ sequence,
        ¬P13BarrierConnectorValid ctx window residual.index sequence := by
  cases classified : classifyP13BarrierConnectors ctx window with
  | complete present => exact present
  | missing residual => exact residual.absent

/-- Coordinatewise product-choice realization for the graph-owned local
connector systems.  This statement quantifies over one independently chosen
connector state per barrier.  It is not a global graph completion and makes
no claim that the 91 choices can be glued or modified simultaneously. -/
def P13CoordinatewiseFlatRealization
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (window : P13SelectedConnectorWindow ctx) : Prop :=
  ∀ assignment : P13BarrierIndex → Bool,
    ∃ choice : ∀ index : P13BarrierIndex,
      P13BarrierConnectorState ctx window index,
      ∀ index,
        p13BarrierConnectorFlat ctx window index (choice index) =
          assignment index

/-- Even the weaker product of unrelated actual connector choices cannot
realize a Boolean cube: target avoidance makes every retained flat bit true. -/
theorem p13CoordinatewiseFlatRealization_impossible
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (window : P13SelectedConnectorWindow ctx) :
    ¬P13CoordinatewiseFlatRealization ctx window := by
  intro realizes
  obtain ⟨choice, values⟩ := realizes (fun _index => false)
  let index : P13BarrierIndex :=
    ⟨(⟨0, by decide⟩, ⟨0, by decide⟩), by
      change P13BarrierAccepted (⟨0, by decide⟩, ⟨0, by decide⟩)
      norm_num [P13BarrierAccepted]⟩
  have actual := p13BarrierConnectorFlat_true ctx window index (choice index)
  have requested := values index
  rw [actual] at requested
  contradiction

/-!
The next required object is intentionally absent: a single finite type of
admissible global graph completions, a map from each completion to all 91
target-test response bits, and a reflection theorem identifying those bits
with the local flat relation.  `P13CoordinatewiseFlatRealization` cannot be
used as that object because its dependent function chooses unrelated paths
inside the already fixed graph and records no gluing operation.
-/

end Erdos64EG.Internal
