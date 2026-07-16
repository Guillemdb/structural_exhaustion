import Erdos64EG.P13ClosureRobustPartIV
import Erdos64EG.P13HotColdInterface
import Erdos64EG.P13MultiScaleConnectorState

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Exact Part-I window-density triage

This file exposes the three arithmetic leaves immediately below the verified
node-`[21]` prefix.  It does not infer the still-open node-`[24]` density
theorem from the 91-row curvature table.  Instead, it fixes the actual packing
as the ceiling and decides the two exact finite predicates required by the
typed node-`[24]` boundary.

The positive leaf is a genuine `VerifiedP13WindowDensityOutput`.  Each
negative leaf retains the same node-`[21]` predecessor and the exact failed
inequality.  Consequently a later cold-skeleton proof cannot silently replace
an obstruction by an assumed density certificate.  The decision performs two
natural-number comparisons and enumerates no vertices, graphs, states,
contexts, or Boolean assignments.
-/

/-- The canonical coverage datum uses the actual CT12 packing number.  This is
bookkeeping only: it does not assert the numerical density cap. -/
noncomputable def p13ExactPackingCoverage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx) :
    P13CoverageResidual ctx (p13MultiScalePackingPrefix node21) where
  windowCeiling := p13 ctx
  packing_le := le_rfl

/-- Exact numerator in the manuscript's normalized high-entropy comparison
after moving the remainder contribution to the right-hand side. -/
def p13HighEntropyRateNumerator : Nat := 116808581006

/-- Exact right-hand numerator `1.5 - 0.1 = 1.4` for the high-entropy
comparison, at the same `10^9` normalization. -/
def p13HighEntropySkeletonNumerator : Nat := 1400000000

/-- The sharper finite cap that a later high-entropy consumer must prove. -/
def P13HighEntropyFiniteCap
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (windowCeiling : Nat) : Prop :=
  p13HighEntropyRateNumerator * windowCeiling ≤
    p13HighEntropySkeletonNumerator * ctx.G.object.input.vertices.card

/-- Exact open high-entropy refinement carried out of node `[24]`.  The
proposition is named and normalized here, but no proof is inserted before the
later high-entropy branch supplies it. -/
structure P13Node24HighEntropyRequirement
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (windowCeiling : Nat) where
  conclusion : Prop
  conclusionExact : conclusion = P13HighEntropyFiniteCap ctx windowCeiling

def p13Node24HighEntropyRequirement
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (windowCeiling : Nat) : P13Node24HighEntropyRequirement ctx windowCeiling where
  conclusion := P13HighEntropyFiniteCap ctx windowCeiling
  conclusionExact := rfl

/-- Exact open terminal consumer carried by node `[23]`: after the retained
realization/gluing requirement is discharged, the entropy comparison must
close this branch. -/
structure P13Node23EntropyOverflowRequirement where
  conclusion : Prop
  conclusionExact : conclusion = False

def p13Node23EntropyOverflowRequirement :
    P13Node23EntropyOverflowRequirement where
  conclusion := False
  conclusionExact := rfl

/-- The three graph-owned producers explicitly left open at node `[160]`. -/
inductive P13Node160OpenProducer
  | localCompletionStates
  | simultaneousResponseRealization
  | commutingWindowGluing
  deriving DecidableEq

/-- Node `[160]`'s exact open requirement tag.  This is not evidence of a
Boolean realization.  It records the graph-owned inputs that the later
completion-state and commuting-gluing producer must consume, so no downstream
node can bypass that missing producer silently. -/
structure P13Node160RealizationRequirement
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx) : Type u where
  previous : VerifiedP13MultiScaleCurvaturePrefix ctx
  previousExact : previous = node21
  packing : VerifiedP13PackingPrefix ctx
  packingExact : packing = p13MultiScalePackingPrefix node21
  barrierCount : p13BarrierClassification.classCount = 91
  openProducers : List P13Node160OpenProducer
  openProducersExact : openProducers =
    [.localCompletionStates, .simultaneousResponseRealization,
      .commutingWindowGluing]

/-- Construct the node-`[160]` handoff from node `[21]`.  The three unit tags
name obligations; they are deliberately not proofs of those obligations. -/
def p13Node160RealizationRequirement
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx) :
    P13Node160RealizationRequirement ctx node21 where
  previous := node21
  previousExact := rfl
  packing := p13MultiScalePackingPrefix node21
  packingExact := rfl
  barrierCount := p13Barrier_class_count
  openProducers := [.localCompletionStates, .simultaneousResponseRealization,
    .commutingWindowGluing]
  openProducersExact := rfl

/-- One graph-owned local completion state.  Its graph, selected-window copy,
support, admissibility, and safe barrier semantics are fixed by the context;
none of these meanings can be chosen by a later certificate author. -/
structure P13Node160LocalGraphCompletion
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (window : SelectedP13Window ctx) where
  object : Graph.FiniteObject ctx.G.Vertex
  windowPath : SimpleGraph.pathGraph 13 ↪g object.graph
  windowExact : ∀ position, windowPath position = window.1 position
  support : Finset ctx.G.Vertex
  windowSupported : ∀ position, window.1 position ∈ support
  outsideSupportPreserved : ∀ left right,
    left ∉ support → right ∉ support →
      (object.graph.Adj left right ↔ ctx.G.object.graph.Adj left right)
  connector : Fin 15 → ctx.G.Vertex
  connectorOutside : ∀ slot position, connector slot ≠ window.1 position
  connectorSupported : ∀ slot, connector slot ∈ support
  connectorSimple : ∀ left right, connector left = connector right → left = right
  connectorAdjacent : ∀ slot : Fin 14,
    object.graph.Adj (connector ⟨slot.1, by omega⟩)
      (connector ⟨slot.1 + 1, by omega⟩)
  safeBarrier : ∀ index : P13BarrierIndex,
    let source := by
      letI : DecidableRel object.graph.Adj := object.input.decideAdj
      exact Graph.InducedPathAttachment.attachmentLabel windowPath
        (connector ⟨0, by decide⟩)
    let middle := by
      letI : DecidableRel object.graph.Adj := object.input.decideAdj
      exact Graph.InducedPathAttachment.attachmentLabel windowPath
        (connector (p13BarrierLeftSlot index))
    let target := by
      letI : DecidableRel object.graph.Adj := object.input.decideAdj
      exact Graph.InducedPathAttachment.attachmentLabel windowPath
        (connector (p13BarrierTotalSlot index))
    P13Legal source ∧ P13Legal middle ∧ P13Legal target ∧
      p13C index.leftLength source middle = 1 ∧
      p13C index.rightLength middle target = 1
  baseline : packedStaticInput.minimumDegree ≤ object.minDegree
  targetAvoiding : ¬PackedTarget (Graph.PackedFiniteObject.pack object)

/-- The response bit is the literal third relation from the node-`[21]`
barrier table, evaluated on the completed graph's own attachment labels. -/
noncomputable def p13Node160LocalResponse
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {window : SelectedP13Window ctx}
    (state : P13Node160LocalGraphCompletion ctx window)
    (index : P13BarrierIndex) : Bool := by
  letI : DecidableRel state.object.graph.Adj := state.object.input.decideAdj
  let source := Graph.InducedPathAttachment.attachmentLabel state.windowPath
    (state.connector ⟨0, by decide⟩)
  let target := Graph.InducedPathAttachment.attachmentLabel state.windowPath
    (state.connector (p13BarrierTotalSlot index))
  exact decide (p13C (index.leftLength + index.rightLength) source target = 1)

/-- A graph-owned global completion into which the local states must commute. -/
structure P13Node160GlobalGraphCompletion
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) where
  object : Graph.FiniteObject ctx.G.Vertex
  windowPath : ∀ window : SelectedP13Window ctx,
    SimpleGraph.pathGraph 13 ↪g object.graph
  windowExact : ∀ window position, windowPath window position = window.1 position
  baseline : packedStaticInput.minimumDegree ≤ object.minDegree
  targetAvoiding : ¬PackedTarget (Graph.PackedFiniteObject.pack object)

/-- The global response uses the glued graph's own selected-window copy and
the exact connector stored by the corresponding interpreted local state. -/
noncomputable def p13Node160GlobalResponse
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    (global : P13Node160GlobalGraphCompletion ctx)
    (window : SelectedP13Window ctx)
    (localState : P13Node160LocalGraphCompletion ctx window)
    (index : P13BarrierIndex) : Bool := by
  letI : DecidableRel global.object.graph.Adj := global.object.input.decideAdj
  let source := Graph.InducedPathAttachment.attachmentLabel
    (global.windowPath window) (localState.connector ⟨0, by decide⟩)
  let target := Graph.InducedPathAttachment.attachmentLabel
    (global.windowPath window)
      (localState.connector (p13BarrierTotalSlot index))
  exact decide (p13C (index.leftLength + index.rightLength) source target = 1)

/-- The full positive payload of node `[160]`.  The finite carrier types may
name a supplied family, but every member is interpreted in the independently
defined graph-completion semantics above.  Realization is quantified over one
supplied assignment and therefore does not enumerate the Boolean cube. -/
structure P13Node160RealizationPackage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx) : Type (u + 1) where
  previous : VerifiedP13MultiScaleCurvaturePrefix ctx
  previousExact : previous = node21
  LocalCompletion : SelectedP13Window ctx → Type u
  localCompletions : ∀ window, FinEnum (LocalCompletion window)
  interpretLocal : ∀ window, LocalCompletion window →
    P13Node160LocalGraphCompletion ctx window
  realizes : ∀ window (assignment : P13BarrierIndex → Bool),
    ∃ state, p13Node160LocalResponse (interpretLocal window state) = assignment
  GlobalCompletion : Type u
  globalCompletions : FinEnum GlobalCompletion
  interpretGlobal : GlobalCompletion → P13Node160GlobalGraphCompletion ctx
  glue : (∀ window, LocalCompletion window) → GlobalCompletion
  restrict : GlobalCompletion → ∀ window, LocalCompletion window
  recover : ∀ choice window, restrict (glue choice) window = choice window
  supportCommutes : ∀ choice window left right,
    left ∈ (interpretLocal window (choice window)).support →
    right ∈ (interpretLocal window (choice window)).support →
      ((interpretGlobal (glue choice)).object.graph.Adj left right ↔
        (interpretLocal window (choice window)).object.graph.Adj left right)
  globalOutsidePreserved : ∀ choice left right,
    (∀ window, left ∉ (interpretLocal window (choice window)).support) →
    (∀ window, right ∉ (interpretLocal window (choice window)).support) →
      ((interpretGlobal (glue choice)).object.graph.Adj left right ↔
        ctx.G.object.graph.Adj left right)
  responseCommutes : ∀ choice window index,
    p13Node160GlobalResponse (interpretGlobal (glue choice)) window
        (interpretLocal window (choice window)) index =
      p13Node160LocalResponse (interpretLocal window (choice window)) index

/-- Node `[160]` is the requested proof-level dichotomy.  The positive branch
carries the full realization/gluing package.  The open branch carries the
exact requirement tag and a proof that this package has not been supplied.
No assignment or state universe is scanned to select the branch. -/
inductive P13Node160RealizationOutcome
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx) : Type (u + 1) where
  | realized (package : P13Node160RealizationPackage ctx node21)
  | openRequirement
      (requirement : P13Node160RealizationRequirement ctx node21)
      (packageAbsent : ¬Nonempty (P13Node160RealizationPackage ctx node21))

noncomputable def p13Node160RealizationDichotomy
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx) :
    P13Node160RealizationOutcome ctx node21 := by
  by_cases available : Nonempty (P13Node160RealizationPackage ctx node21)
  · exact .realized (Classical.choice available)
  · exact .openRequirement (p13Node160RealizationRequirement node21) available

theorem p13Node160RealizationDichotomy_exhaustive
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx) :
    (∃ package, p13Node160RealizationDichotomy node21 = .realized package) ∨
      (∃ requirement absent, p13Node160RealizationDichotomy node21 =
        .openRequirement requirement absent) := by
  cases outcome : p13Node160RealizationDichotomy node21 with
  | realized package => exact Or.inl ⟨package, rfl⟩
  | openRequirement requirement absent =>
      exact Or.inr ⟨requirement, absent, rfl⟩

/-!
## Diagram nodes [22]--[24]

The first-part diagram uses these nodes as a directed arithmetic split, not as
the later proof that the overflow constructor is impossible.  Node `[22]`
decides the literal finite window-density comparison on the exact packing
retained by node `[21]`.  Its two proof-carrying constructors are the complete
local responsibilities of nodes `[23]` and `[24]`:

* node `[23]` retains the strict overflow inequality for the later window
  entropy consumer;
* node `[24]` retains the complementary finite density ceiling for the later
  remainder and hot/cold consumers.

No Boolean assignment, completion state, graph family, or ambient universe is
inspected here.  In particular, this split neither asserts the still-open
91-coordinate commuting realization nor closes the downstream overflow
branch.
-/

/-- Node `[23]`: the exact density-overflow payload selected by node `[22]`.
The entropy contradiction is a later consumer of this payload. -/
structure VerifiedP13Node23DensityOverflow
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx) : Type (u + 1) where
  previous : VerifiedP13MultiScaleCurvaturePrefix ctx
  previousExact : previous = node21
  coverage : P13CoverageResidual ctx (p13MultiScalePackingPrefix node21)
  coverageExact : coverage = p13ExactPackingCoverage ctx node21
  failedCap : ¬P13WindowDensityFiniteCap ctx coverage.windowCeiling
  entropyOverflow : P13Node23EntropyOverflowRequirement

/-- Node `[24]`: the exact complementary density-ceiling payload selected by
node `[22]`.  It is deliberately weaker than the later structural theorem,
which must additionally supply the strict-quarter hot/cold budget. -/
structure VerifiedP13Node24DensityHandoff
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx) : Type (u + 1) where
  previous : VerifiedP13MultiScaleCurvaturePrefix ctx
  previousExact : previous = node21
  coverage : P13CoverageResidual ctx (p13MultiScalePackingPrefix node21)
  coverageExact : coverage = p13ExactPackingCoverage ctx node21
  densityCap : P13WindowDensityFiniteCap ctx coverage.windowCeiling
  highEntropy : P13Node24HighEntropyRequirement ctx coverage.windowCeiling

/-- Node `[22]`: the manuscript's exhaustive "packing density too large?"
decision, with each edge carrying the exact same-context successor payload. -/
inductive P13Node22DensityOutcome
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx) : Type (u + 1) where
  | tooLarge (node23 : VerifiedP13Node23DensityOverflow ctx node21)
  | withinCap (node24 : VerifiedP13Node24DensityHandoff ctx node21)

/-- Select node `[22]` by the exact natural-number dichotomy. -/
noncomputable def runP13Node22DensityDecision
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx) :
    P13Node22DensityOutcome ctx node21 := by
  let coverage := p13ExactPackingCoverage ctx node21
  by_cases cap : P13WindowDensityFiniteCap ctx coverage.windowCeiling
  · exact .withinCap ⟨node21, rfl, coverage, rfl, cap,
      p13Node24HighEntropyRequirement ctx coverage.windowCeiling⟩
  · exact .tooLarge ⟨node21, rfl, coverage, rfl, cap,
      p13Node23EntropyOverflowRequirement⟩

/-- Node `[23]` exposes the strict reverse comparison, with no division or
floating-point normalization. -/
theorem VerifiedP13Node23DensityOverflow.strict
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    (node23 : VerifiedP13Node23DensityOverflow ctx node21) :
    p13WindowDensitySkeletonNumerator * ctx.G.object.input.vertices.card <
      p13WindowDensityRateNumerator * node23.coverage.windowCeiling := by
  exact Nat.lt_of_not_ge node23.failedCap

/-- Node `[24]` bounds the actual selected packing by the exact finite density
ceiling on its branch. -/
theorem VerifiedP13Node24DensityHandoff.packingDensityCap
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    (node24 : VerifiedP13Node24DensityHandoff ctx node21) :
    p13WindowDensityRateNumerator * p13 ctx ≤
      p13WindowDensitySkeletonNumerator * ctx.G.object.input.vertices.card := by
  exact (Nat.mul_le_mul_left p13WindowDensityRateNumerator
    node24.coverage.packing_le).trans node24.densityCap

/-- Exact manuscript connector `[24] \to [25] \to \cdots \to [47]`.

The node-`[24]` branch already owns the selected packing and its coverage
certificate.  This definition feeds that literal certificate to the existing
same-context remainder/rank construction.  It introduces no new finite
universe and does not replace the retained realization or density evidence. -/
noncomputable def VerifiedP13Node24DensityHandoff.globalRankPrefix
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    (node24 : VerifiedP13Node24DensityHandoff ctx node21) :
    P13DensityConnectedGlobalRankPrefix ctx node21 node24.coverage :=
  p13DensityConnectedGlobalRankPrefix ctx node21 node24.coverage

/-- The terminal count on the connected node-`[47]` prefix is exactly the
CT15 full-rank count, now indexed by node `[24]`'s own coverage residual. -/
theorem VerifiedP13Node24DensityHandoff.globalRankPrefix_fullRankCount
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    (node24 : VerifiedP13Node24DensityHandoff ctx node21) :
    (p13CurvatureResponseProfile ctx).ct15Profile.coordinates.card =
      (p13RemainderCurvatureProfile ctx).wedgeCount :=
  densityConnected_fullRankCount node24.globalRankPrefix

/-- The decision has exactly the two manuscript successors. -/
theorem runP13Node22DensityDecision_exhaustive
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx) :
    (∃ node23, runP13Node22DensityDecision ctx node21 = .tooLarge node23) ∨
      (∃ node24, runP13Node22DensityDecision ctx node21 = .withinCap node24) := by
  cases outcome : runP13Node22DensityDecision ctx node21 with
  | tooLarge node23 => exact Or.inl ⟨node23, rfl⟩
  | withinCap node24 => exact Or.inr ⟨node24, rfl⟩

/-- Exact exhaustive routing boundary below node `[21]`.

* `certified` contains all fields required by node `[24]`;
* `densityOverflow` is the literal failure of the printed finite density cap;
* `quarterObstruction` retains the density cap but records failure of the
  strict quarter-budget inequality.
-/
inductive P13PartIWindowDensityOutcome
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx) : Type u where
  | certified
      (output : VerifiedP13WindowDensityOutput ctx node21)
  | densityOverflow
      (coverage : P13CoverageResidual ctx
        (p13MultiScalePackingPrefix node21))
      (failedCap : ¬P13WindowDensityFiniteCap ctx coverage.windowCeiling)
  | quarterObstruction
      (coverage : P13CoverageResidual ctx
        (p13MultiScalePackingPrefix node21))
      (densityCap : P13WindowDensityFiniteCap ctx coverage.windowCeiling)
      (failedQuarter :
        ¬P13QuarterNetBudget ctx (node21 := node21) coverage)

/-- Execute the exact two-comparison trichotomy. -/
noncomputable def runP13PartIWindowDensityTriage
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx) :
    P13PartIWindowDensityOutcome ctx node21 := by
  let coverage := p13ExactPackingCoverage ctx node21
  by_cases densityCap :
      P13WindowDensityFiniteCap ctx coverage.windowCeiling
  · by_cases quarter :
        P13QuarterNetBudget ctx (node21 := node21) coverage
    · exact .certified ⟨⟨coverage, densityCap, quarter⟩⟩
    · exact .quarterObstruction coverage densityCap quarter
  · exact .densityOverflow coverage densityCap

/-- The overflow leaf is the strict reverse of the finite density cap. -/
theorem P13PartIWindowDensityOutcome.densityOverflow_strict
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    {coverage : P13CoverageResidual ctx
      (p13MultiScalePackingPrefix node21)}
    (failedCap : ¬P13WindowDensityFiniteCap ctx coverage.windowCeiling) :
    p13WindowDensitySkeletonNumerator *
        ctx.G.object.input.vertices.card <
      p13WindowDensityRateNumerator * coverage.windowCeiling := by
  exact Nat.lt_of_not_ge failedCap

/-- The quarter-obstruction leaf is the non-strict reverse of the strict
quarter-budget inequality. -/
theorem P13PartIWindowDensityOutcome.quarterObstruction_le
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    {coverage : P13CoverageResidual ctx
      (p13MultiScalePackingPrefix node21)}
    (failedQuarter :
      ¬P13QuarterNetBudget ctx (node21 := node21) coverage) :
    coverage.remainderFloor ≤
      4 * p13CoverageNetBudgetUpper ctx (node21 := node21) coverage := by
  exact Nat.le_of_not_gt failedQuarter

/-- Every certified leaf composes through the already verified Part-IV
strict-quarter handoff without any Boolean-product premise. -/
noncomputable def P13PartIWindowDensityOutcome.certifiedHandoff
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    (output : VerifiedP13WindowDensityOutput ctx node21) :
    P13QuarterNetDeficiencyHandoff ctx node21 output.coverage :=
  p13ClosureRobustPartIV output

end Erdos64EG.Internal
