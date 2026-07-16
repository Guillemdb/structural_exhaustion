import Erdos64EG.P13SameWindowLongSupportPrefix
import StructuralExhaustion.Routes.LongPrefixObservedLabel

namespace Erdos64EG.Internal

open StructuralExhaustion
open StructuralExhaustion.Graph

universe u

/-!
# Node [164]: observed long-prefix labels and refinement frontier

This node consumes the exact node-`[163]` run.  Every position of its forced
`Q_base + 1` prefix is mapped back to the literal corridor support.  A small
executable classifier then inspects the first nine of those ordered
occurrences using the graph-derived label

`(ambient degree mod 4, membership in the selected P13 packing)`.

There are eight such labels, so the first nine actual occurrences contain a
repeat.  The output is intentionally a typed semantic-refinement residual:
coarse-label equality is not asserted to be D4--D7 response equality and no
CT8 removal is manufactured.
-/

variable {ctx : Core.MinimalCounterexampleContext
  PackedProblem.{u} PackedTarget.{u}}
variable {previous : VerifiedP13MultiScaleCurvaturePrefix ctx}
variable {window : P13ActualSelectedWindow ctx}

/-- Exact predecessor retained by node `[164]`; callers cannot replace it by
an arbitrary long-support source. -/
structure P13SameWindowLongPrefixStateSource
    (fork : P13ActualAttachmentColdFork ctx previous window)
    (quiet : P13SameWindowQuietOutput fork)
    (long : P13SameWindowLongOutput fork quiet) where
  node163 : P13SameWindowLongSupportPrefix fork quiet long
  node163Exact : node163 = runP13SameWindowLongSupportPrefix fork quiet long

noncomputable def p13SameWindowLongPrefixStateSource
    (fork : P13ActualAttachmentColdFork ctx previous window)
    (quiet : P13SameWindowQuietOutput fork)
    (long : P13SameWindowLongOutput fork quiet) :
    P13SameWindowLongPrefixStateSource fork quiet long :=
  ⟨runP13SameWindowLongSupportPrefix fork quiet long, rfl⟩

variable {fork : P13ActualAttachmentColdFork ctx previous window}
variable {quiet : P13SameWindowQuietOutput fork}
variable {long : P13SameWindowLongOutput fork quiet}

theorem p13SameWindowLongPrefixStateSource_exactNode163
    (source : P13SameWindowLongPrefixStateSource fork quiet long) :
    source.node163 = runP13SameWindowLongSupportPrefix fork quiet long :=
  source.node163Exact

/-- The identical graph-owned corridor support consumed from node `[163]`. -/
noncomputable abbrev p13SameWindowLongCorridorSupport :=
  ((p13SelectedWindowCorridorProducer ctx).ambientReturn quiet.stub).support

theorem p13SameWindowLongPrefixSource_supportLength
    (source : P13SameWindowLongPrefixStateSource fork quiet long) :
    source.node163.handoff.source.supportLength =
      (p13SameWindowLongCorridorSupport (ctx := ctx) (quiet := quiet)).length := by
  rw [source.node163.exactSource]
  rfl

theorem p13SameWindowLongPrefixSource_scale
    (source : P13SameWindowLongPrefixStateSource fork quiet long) :
    source.node163.handoff.source.scale = p13ColdD1D3BaseThreshold := by
  rw [source.node163.exactSource]
  rfl

/-- Exact embedding of every forced prefix index into the literal corridor
support retained by `quiet`. -/
noncomputable def p13SameWindowLongPrefixSupportPosition
    (source : P13SameWindowLongPrefixStateSource fork quiet long)
    (position : Routes.LongFiniteSupportHandoff.PrefixPosition
      source.node163.handoff.source) :
    Fin (p13SameWindowLongCorridorSupport (ctx := ctx) (quiet := quiet)).length :=
  Fin.cast (p13SameWindowLongPrefixSource_supportLength source)
    (Routes.LongFiniteSupportHandoff.prefixEmbedding
      source.node163.handoff.source position)

@[simp]
theorem p13SameWindowLongPrefixSupportPosition_val
    (source : P13SameWindowLongPrefixStateSource fork quiet long)
    (position : Routes.LongFiniteSupportHandoff.PrefixPosition
      source.node163.handoff.source) :
    (p13SameWindowLongPrefixSupportPosition source position).1 = position.1 :=
  rfl

/-- Literal graph vertex at one exact forced-prefix occurrence. -/
noncomputable def p13SameWindowLongPrefixVertex
    (source : P13SameWindowLongPrefixStateSource fork quiet long)
    (position : Routes.LongFiniteSupportHandoff.PrefixPosition
      source.node163.handoff.source) : ctx.G.Vertex :=
  (p13SameWindowLongCorridorSupport (ctx := ctx) (quiet := quiet)).get
    (p13SameWindowLongPrefixSupportPosition source position)

/-- Complete pointwise occurrence record for the full `Q_base + 1` prefix.
It retains both positions, the literal vertex, and the two local graph
coordinates used by the honest coarse classifier. -/
structure P13SameWindowLongPrefixOccurrence
    (source : P13SameWindowLongPrefixStateSource fork quiet long) where
  prefixPosition : Routes.LongFiniteSupportHandoff.PrefixPosition
    source.node163.handoff.source
  supportPosition : Fin
    (p13SameWindowLongCorridorSupport (ctx := ctx) (quiet := quiet)).length
  positionExact : supportPosition =
    p13SameWindowLongPrefixSupportPosition source prefixPosition
  vertex : ctx.G.Vertex
  vertexExact : vertex =
    p13SameWindowLongPrefixVertex source prefixPosition
  degreeResidue : Fin 4
  degreeResidueExact : degreeResidue =
    ⟨ctx.G.object.degree vertex % 4, Nat.mod_lt _ (by decide)⟩
  covered : Bool
  coveredIff : covered = true ↔ vertex ∈ p13CoveredVertices ctx

/-- Construct the exact occurrence locally from one prefix position. -/
noncomputable def p13SameWindowLongPrefixOccurrence
    (source : P13SameWindowLongPrefixStateSource fork quiet long)
    (position : Routes.LongFiniteSupportHandoff.PrefixPosition
      source.node163.handoff.source) :
    P13SameWindowLongPrefixOccurrence source where
  prefixPosition := position
  supportPosition := p13SameWindowLongPrefixSupportPosition source position
  positionExact := rfl
  vertex := p13SameWindowLongPrefixVertex source position
  vertexExact := rfl
  degreeResidue :=
    ⟨ctx.G.object.degree (p13SameWindowLongPrefixVertex source position) % 4,
      Nat.mod_lt _ (by decide)⟩
  degreeResidueExact := rfl
  covered := by
    letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
    exact decide
      (p13SameWindowLongPrefixVertex source position ∈ p13CoveredVertices ctx)
  coveredIff := by
    letI : DecidableEq ctx.G.Vertex := ctx.G.object.input.vertices.decEq
    simp

/-- The full authored occurrence universe has exactly `Q_base + 1` elements.
It is used as a type/cardinality fact, not materialized by the runner. -/
theorem p13SameWindowLongPrefixOccurrence_card
    (source : P13SameWindowLongPrefixStateSource fork quiet long) :
    Fintype.card (Routes.LongFiniteSupportHandoff.PrefixPosition
      source.node163.handoff.source) = p13ColdD1D3BaseThreshold + 1 := by
  rw [Fintype.card_fin, p13SameWindowLongPrefixSource_scale source]

/-- Canonical declared-order enumeration of every full-prefix position.  The
runner does not materialize this 22-million-entry list. -/
@[implicit_reducible]
def p13SameWindowLongFullPrefixPositions
    (source : P13SameWindowLongPrefixStateSource fork quiet long) :
    FinEnum (Routes.LongFiniteSupportHandoff.PrefixPosition
      source.node163.handoff.source) :=
  Routes.LongFiniteSupportHandoff.prefixPositions source.node163.handoff.source

theorem p13SameWindowLongFullPrefixPositions_exhaustive
    (source : P13SameWindowLongPrefixStateSource fork quiet long)
    (position : Routes.LongFiniteSupportHandoff.PrefixPosition
      source.node163.handoff.source) :
    position ∈ (p13SameWindowLongFullPrefixPositions source).orderedValues :=
  (p13SameWindowLongFullPrefixPositions source).mem_orderedValues position

theorem p13SameWindowLongFullPrefixPositions_nodup
    (source : P13SameWindowLongPrefixStateSource fork quiet long) :
    (p13SameWindowLongFullPrefixPositions source).orderedValues.Nodup :=
  (p13SameWindowLongFullPrefixPositions source).nodup_orderedValues

/-- Node `[163]` forces at least nine literal corridor entries. -/
theorem p13SameWindowLongPrefix_firstNine
    (source : P13SameWindowLongPrefixStateSource fork quiet long) :
    9 ≤ (p13SameWindowLongCorridorSupport
      (ctx := ctx) (quiet := quiet)).length := by
  have exceeds := source.node163.handoff.source.exceeds
  rw [p13SameWindowLongPrefixSource_scale source,
    p13SameWindowLongPrefixSource_supportLength source] at exceeds
  norm_num [p13ColdD1D3BaseThreshold] at exceeds ⊢
  omega

/-- Generic graph-owned classifier input.  Its only observations are entries
of the identical corridor and the exact selected-packing vertex set. -/
noncomputable def p13SameWindowLongPrefixObservedInput
    (source : P13SameWindowLongPrefixStateSource fork quiet long) :
    Graph.LongPrefixObservedLabel.Input ctx.G.object where
  support := p13SameWindowLongCorridorSupport (ctx := ctx) (quiet := quiet)
  marked := p13CoveredVertices ctx
  firstNine := p13SameWindowLongPrefix_firstNine source

/-- Embed each classifier occurrence into the actual node-`[163]` prefix. -/
def p13SameWindowLongPrefixFirstNineEmbedding
    (source : P13SameWindowLongPrefixStateSource fork quiet long)
    (occurrence : Graph.LongPrefixObservedLabel.Occurrence) :
    Routes.LongFiniteSupportHandoff.PrefixPosition
      source.node163.handoff.source := by
  refine ⟨occurrence.1, ?_⟩
  rw [p13SameWindowLongPrefixSource_scale source]
  norm_num [p13ColdD1D3BaseThreshold] at occurrence ⊢
  omega

@[simp]
theorem p13SameWindowLongPrefixFirstNineEmbedding_val
    (source : P13SameWindowLongPrefixStateSource fork quiet long)
    (occurrence : Graph.LongPrefixObservedLabel.Occurrence) :
    (p13SameWindowLongPrefixFirstNineEmbedding source occurrence).1 = occurrence.1 :=
  rfl

theorem p13SameWindowLongPrefixFirstNineEmbedding_injective
    (source : P13SameWindowLongPrefixStateSource fork quiet long) :
    Function.Injective (p13SameWindowLongPrefixFirstNineEmbedding source) := by
  intro left right equal
  apply Fin.ext
  simpa using congrArg Fin.val equal

/-- The generic observed vertex is definitionally the literal node-`[163]`
corridor entry at the embedded full-prefix position. -/
theorem p13SameWindowLongPrefixObservedVertex_exact
    (source : P13SameWindowLongPrefixStateSource fork quiet long)
    (occurrence : Graph.LongPrefixObservedLabel.Occurrence) :
    Graph.LongPrefixObservedLabel.vertex
        (p13SameWindowLongPrefixObservedInput source) occurrence =
      p13SameWindowLongPrefixVertex source
        (p13SameWindowLongPrefixFirstNineEmbedding source occurrence) := by
  unfold Graph.LongPrefixObservedLabel.vertex
    Graph.LongPrefixObservedLabel.supportPosition
    p13SameWindowLongPrefixVertex
    p13SameWindowLongPrefixSupportPosition
  congr 1

/-- Exact node-`[164]` output.  Its route is indexed by the unchanged branch
context and terminates at the semantic-refinement frontier. -/
structure P13SameWindowLongPrefixStateLabels
    (source : P13SameWindowLongPrefixStateSource fork quiet long) where
  routed : Routes.LongPrefixObservedLabel.Residual ctx.toBranchContext
    (p13SameWindowLongPrefixObservedInput source)
  exactRoute : routed = Routes.LongPrefixObservedLabel.route
    ⟨Graph.LongPrefixObservedLabel.run
      (p13SameWindowLongPrefixObservedInput source)⟩

noncomputable def runP13SameWindowLongPrefixStateLabels
    (source : P13SameWindowLongPrefixStateSource fork quiet long) :
    P13SameWindowLongPrefixStateLabels source where
  routed := Routes.LongPrefixObservedLabel.route
    ⟨Graph.LongPrefixObservedLabel.run
      (p13SameWindowLongPrefixObservedInput source)⟩
  exactRoute := rfl

/-- The total leaf retains two distinct actual prefix positions. -/
theorem runP13SameWindowLongPrefixStateLabels_distinct
    (source : P13SameWindowLongPrefixStateSource fork quiet long) :
    let repetition :=
      (runP13SameWindowLongPrefixStateLabels source).routed.refinement.repetition
    p13SameWindowLongPrefixFirstNineEmbedding source repetition.collision.first ≠
      p13SameWindowLongPrefixFirstNineEmbedding source repetition.collision.second := by
  dsimp only
  intro equal
  apply Graph.LongPrefixObservedLabel.run_distinct
    (p13SameWindowLongPrefixObservedInput source)
  exact p13SameWindowLongPrefixFirstNineEmbedding_injective source equal

/-- The total leaf proves equality only of the two graph-derived coarse
labels; this theorem deliberately says nothing about D4--D7 responses. -/
theorem runP13SameWindowLongPrefixStateLabels_sameCoarseLabel
    (source : P13SameWindowLongPrefixStateSource fork quiet long) :
    let repetition :=
      (runP13SameWindowLongPrefixStateLabels source).routed.refinement.repetition
    Graph.LongPrefixObservedLabel.label
        (p13SameWindowLongPrefixObservedInput source) repetition.collision.first =
      Graph.LongPrefixObservedLabel.label
        (p13SameWindowLongPrefixObservedInput source) repetition.collision.second := by
  dsimp only
  exact Graph.LongPrefixObservedLabel.run_sameLabel _

theorem runP13SameWindowLongPrefixStateLabels_ct10_terminal
    (source : P13SameWindowLongPrefixStateSource fork quiet long) :
    (runP13SameWindowLongPrefixStateLabels source).routed.classification.terminal =
      .promoted := by
  rw [(runP13SameWindowLongPrefixStateLabels source).routed.classificationExact]
  exact Routes.LongPrefixObservedLabel.semantic_terminal_promoted _ _

theorem runP13SameWindowLongPrefixStateLabels_ct10_trace
    (source : P13SameWindowLongPrefixStateSource fork quiet long) :
    (runP13SameWindowLongPrefixStateLabels source).routed.classification.trace =
      [.entry, .table, .direct, .missing, .promotion, .promotedTerminal] := by
  rw [(runP13SameWindowLongPrefixStateLabels source).routed.classificationExact]
  exact Routes.LongPrefixObservedLabel.semantic_run_trace _ _

theorem runP13SameWindowLongPrefixStateLabels_ct10_verified
    (source : P13SameWindowLongPrefixStateSource fork quiet long) :
    (runP13SameWindowLongPrefixStateLabels source).routed.classification.outcome.Valid := by
  rw [(runP13SameWindowLongPrefixStateLabels source).routed.classificationExact]
  exact Routes.LongPrefixObservedLabel.semantic_run_verified _ _

theorem runP13SameWindowLongPrefixStateLabels_ct10_trace_valid
    (source : P13SameWindowLongPrefixStateSource fork quiet long) :
    CT10.Graph.ValidTrace (Routes.LongPrefixObservedLabel.semanticCapability _)
      (Routes.LongPrefixObservedLabel.semanticInput ctx.toBranchContext
        (Graph.LongPrefixObservedLabel.run
          (p13SameWindowLongPrefixObservedInput source)))
      (runP13SameWindowLongPrefixStateLabels source).routed.classification.trace := by
  rw [(runP13SameWindowLongPrefixStateLabels source).routed.classificationExact]
  exact Routes.LongPrefixObservedLabel.semantic_run_trace_valid _ _

noncomputable def runP13SameWindowLongPrefixStateLabels_ct10_total
    (source : P13SameWindowLongPrefixStateSource fork quiet long) :=
  Routes.LongPrefixObservedLabel.semantic_run_total ctx.toBranchContext
    (Graph.LongPrefixObservedLabel.run
      (p13SameWindowLongPrefixObservedInput source))

/-- The classifier uses a fixed 36-pair observed scan with two uncached
graph-local label evaluations per comparison; it is linear in the selected
graph size and independent of `Q_base`. -/
theorem runP13SameWindowLongPrefixStateLabels_visibleChecks
    (source : P13SameWindowLongPrefixStateSource fork quiet long) :
    Graph.LongPrefixObservedLabel.visibleChecks
        (p13SameWindowLongPrefixObservedInput source) ≤
      144 * (ctx.G.object.input.vertices.card + 1) :=
  Graph.LongPrefixObservedLabel.visibleChecks_le _

/-- The retained CT10 classification contributes nine further conservative
class/row checks on exactly the two collided occurrences. -/
theorem runP13SameWindowLongPrefixStateLabels_totalVisibleChecks
    (source : P13SameWindowLongPrefixStateSource fork quiet long) :
    Graph.LongPrefixObservedLabel.visibleChecks
        (p13SameWindowLongPrefixObservedInput source) +
      Routes.LongPrefixObservedLabel.semanticChecks
        (runP13SameWindowLongPrefixStateLabels source).routed.refinement ≤
      144 * (ctx.G.object.input.vertices.card + 1) + 9 := by
  have visible := runP13SameWindowLongPrefixStateLabels_visibleChecks source
  rw [Routes.LongPrefixObservedLabel.semanticChecks_eq_nine]
  omega

/-- The routed node preserves the identical selected minimal-counterexample
graph by dependent branch-context indexing. -/
theorem runP13SameWindowLongPrefixStateLabels_ambient_preserved
    (_source : P13SameWindowLongPrefixStateSource fork quiet long) :
    ctx.toBranchContext.G = ctx.G := rfl

end Erdos64EG.Internal
