import Erdos64EG.P13ClosureRobustPartIV
import StructuralExhaustion.Core.ExactHandoff
import Erdos64EG.P13HotColdInterface
import Erdos64EG.P13MultiScaleConnectorState
import Erdos64EG.P13WeightedHotColdInterface

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

/-- One graph-owned local completion state.  Its graph, selected-window copy,
support, admissibility, and safe barrier semantics are fixed by the context;
none of these meanings can be chosen by a later certificate author. -/
structure P13LocalGraphCompletion
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
noncomputable def p13LocalResponse
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {window : SelectedP13Window ctx}
    (state : P13LocalGraphCompletion ctx window)
    (index : P13BarrierIndex) : Bool := by
  letI : DecidableRel state.object.graph.Adj := state.object.input.decideAdj
  let source := Graph.InducedPathAttachment.attachmentLabel state.windowPath
    (state.connector ⟨0, by decide⟩)
  let target := Graph.InducedPathAttachment.attachmentLabel state.windowPath
    (state.connector (p13BarrierTotalSlot index))
  exact decide (p13C (index.leftLength + index.rightLength) source target = 1)

/-- A graph-owned global completion into which the local states must commute. -/
structure P13GlobalGraphCompletion
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) where
  object : Graph.FiniteObject ctx.G.Vertex
  windowPath : ∀ window : SelectedP13Window ctx,
    SimpleGraph.pathGraph 13 ↪g object.graph
  windowExact : ∀ window position, windowPath window position = window.1 position
  baseline : packedStaticInput.minimumDegree ≤ object.minDegree
  targetAvoiding : ¬PackedTarget (Graph.PackedFiniteObject.pack object)

/-- The untouched counterexample is the empty hot aggregate's canonical
global completion.  This is the base case for the packing-order compatibility
ledger; it enumerates neither completions nor graphs. -/
noncomputable def p13OriginalGlobalCompletion
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    P13GlobalGraphCompletion ctx where
  object := ctx.G.object
  windowPath := fun window => window.1
  windowExact := by intros; rfl
  baseline := ctx.baseline
  targetAvoiding := ctx.avoids

/-- The global response uses the glued graph's own selected-window copy and
the exact connector stored by the corresponding interpreted local state. -/
noncomputable def p13GlobalResponse
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    (global : P13GlobalGraphCompletion ctx)
    (window : SelectedP13Window ctx)
    (localState : P13LocalGraphCompletion ctx window)
    (index : P13BarrierIndex) : Bool := by
  letI : DecidableRel global.object.graph.Adj := global.object.input.decideAdj
  let source := Graph.InducedPathAttachment.attachmentLabel
    (global.windowPath window) (localState.connector ⟨0, by decide⟩)
  let target := Graph.InducedPathAttachment.attachmentLabel
    (global.windowPath window)
      (localState.connector (p13BarrierTotalSlot index))
  exact decide (p13C (index.leftLength + index.rightLength) source target = 1)

/-!
## Diagram nodes [22]--[24]

The first-part diagram starts with a directed arithmetic split.  Node `[22]`
decides the literal finite window-density comparison on the exact packing
retained by node `[21]`.  Its two proof-carrying constructors are exact inputs
to the still-open original claims at nodes `[23]` and `[24]`:

* the node-`[23]` input retains the strict overflow inequality for the window
  entropy contradiction;
* the node-`[24]` input retains the complementary finite density ceiling for
  the full window-density and high-entropy theorem.

No Boolean assignment, completion state, graph family, or ambient universe is
inspected here.  Consequently this file completes node `[22]` only: it neither
asserts the still-open 91-coordinate commuting realization, closes node `[23]`,
nor proves the quantitative conclusions displayed in node `[24]`.
-/

/-- Node `[23]`: the exact density-overflow payload selected by node `[22]`.
The entropy contradiction is a later consumer of this payload. -/
structure VerifiedP13Node23DensityOverflow
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx) : Type (u + 4)
    extends Core.ExactHandoff node21 where
  coverage : P13CoverageResidual ctx (p13MultiScalePackingPrefix node21)
  coverageExact : coverage = p13ExactPackingCoverage ctx node21
  failedCap : ¬P13WindowDensityFiniteCap ctx coverage.windowCeiling
  entropyOverflow : P13Node23EntropyOverflowRequirement

/-- Node `[24]`: the exact complementary density-ceiling payload selected by
node `[22]`.  It is deliberately weaker than the later structural theorem,
which must additionally supply the strict-quarter hot/cold budget. -/
structure VerifiedP13Node24DensityHandoff
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx) : Type (u + 4)
    extends Core.ExactHandoff node21 where
  coverage : P13CoverageResidual ctx (p13MultiScalePackingPrefix node21)
  coverageExact : coverage = p13ExactPackingCoverage ctx node21
  densityCap : P13WindowDensityFiniteCap ctx coverage.windowCeiling
  highEntropy : P13Node24HighEntropyRequirement ctx coverage.windowCeiling

/-- Node `[22]`: the manuscript's exhaustive "packing density too large?"
decision, with each edge carrying the exact same-context successor payload. -/
inductive P13Node22DensityOutcome
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx) : Type (u + 4) where
  | tooLarge (node23 : VerifiedP13Node23DensityOverflow ctx node21)
  | withinCap (node24 : VerifiedP13Node24DensityHandoff ctx node21)

/-- Select node `[22]` by the exact natural-number dichotomy. -/
noncomputable def runP13Node22DensityDecision
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx) :
    P13Node22DensityOutcome ctx node21 := by
  let coverage := p13ExactPackingCoverage ctx node21
  by_cases cap : P13WindowDensityFiniteCap ctx coverage.windowCeiling
  · exact .withinCap ⟨⟨node21, rfl⟩, coverage, rfl, cap,
      p13Node24HighEntropyRequirement ctx coverage.windowCeiling⟩
  · exact .tooLarge ⟨⟨node21, rfl⟩, coverage, rfl, cap,
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

/-- Exact node-`[149]`/`[150]` arithmetic handoff.  If the still-separate
semantic hot aggregator proves that the exact weighted-hot list fits in the
window skeleton budget, node `[23]`'s strict total overflow forces a genuine
weighted-cold window on the identical node-`[21]` packing. -/
theorem VerifiedP13Node23DensityOverflow.hotBudget_forces_cold_nonempty
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    (node23 : VerifiedP13Node23DensityOverflow ctx node21)
    (hotBound : p13WindowDensityRateNumerator *
        (p13WeightedHotWindows ctx node21).length ≤
      p13WindowDensitySkeletonNumerator *
        ctx.G.object.input.vertices.card) :
    0 < (p13WeightedColdWindows ctx node21).length := by
  have ceilingExact : node23.coverage.windowCeiling = p13 ctx := by
    rw [node23.coverageExact]
    rfl
  have overflow : p13WindowDensitySkeletonNumerator *
        ctx.G.object.input.vertices.card <
      p13WindowDensityRateNumerator * p13 ctx := by
    simpa [ceilingExact] using node23.strict
  exact p13WeightedHotOverflow_forces_cold_nonempty ctx node21
    p13WindowDensityRateNumerator
    (p13WindowDensitySkeletonNumerator * ctx.G.object.input.vertices.card)
    hotBound overflow

/-- Quantitative node-`[150]` handoff in exact integer form.  The excess of
the total window demand over the labelled-skeleton budget is paid by the
identical weighted-cold list.  Normalizing this inequality is the paper's
`C >= (theta - theta_win) n - o(n)` statement; keeping it integral avoids
rounding and preserves the exact predecessor objects. -/
theorem VerifiedP13Node23DensityOverflow.hotBudget_shortfall_le_cold
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    (node23 : VerifiedP13Node23DensityOverflow ctx node21)
    (hotBound : p13WindowDensityRateNumerator *
        (p13WeightedHotWindows ctx node21).length <=
      p13WindowDensitySkeletonNumerator *
        ctx.G.object.input.vertices.card) :
    p13WindowDensityRateNumerator * p13 ctx -
        p13WindowDensitySkeletonNumerator * ctx.G.object.input.vertices.card <=
      p13WindowDensityRateNumerator *
        (p13WeightedColdWindows ctx node21).length := by
  exact p13WeightedHotBudget_shortfall_le_cold ctx node21
    p13WindowDensityRateNumerator
    (p13WindowDensitySkeletonNumerator * ctx.G.object.input.vertices.card)
    hotBound

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
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx) : Type (u + 4) where
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
