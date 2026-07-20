import Erdos64EG.Future.P13SameWindowStructuralFrontier

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Exact node-[21] to Part-XI same-window route

This is a thin provenance adapter for the already graph-owned thirteen-bit
actual-attachment classifier.  For every window in the exact CT12 packing it
retains the node-[21] prefix, the classifier-produced cold residual, and the
computed node-[159] structural continuation on that same window and graph.

It is deliberately not the node-[22] ninety-one-barrier realization
interface.  In particular, it proves no window entropy, packing-density bound,
or node-[23] overflow.  Its purpose is to make the valid parallel handoff to
Part XI explicit without identifying a missing actual-adjacency vector with a
missing multi-scale completion assignment.
-/

/-- One exact same-context route entry for one member of the CT12-selected
packing.  The equalities make both computations unavoidable provenance, rather
than caller-authored residuals. -/
structure P13Node21PartXIEntry
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedP13MultiScaleCurvaturePrefix ctx) where
  window : P13ActualSelectedWindow ctx
  fork : P13ActualAttachmentColdFork ctx previous window
  forkExact : fork = p13ActualAttachmentColdFork ctx previous window
  frontier : P13SameWindowStructuralFrontier fork
  frontierExact : frontier = runP13SameWindowStructuralFrontier fork

/-- Execute the actual-attachment cold fork and its graph-owned structural
continuation for one exact selected window. -/
noncomputable def p13Node21PartXIEntry
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedP13MultiScaleCurvaturePrefix ctx)
    (window : P13ActualSelectedWindow ctx) :
    P13Node21PartXIEntry ctx previous where
  window := window
  fork := p13ActualAttachmentColdFork ctx previous window
  forkExact := rfl
  frontier := runP13SameWindowStructuralFrontier
    (p13ActualAttachmentColdFork ctx previous window)
  frontierExact := rfl

/-- Every route entry retains a genuine missing assignment of the literal
thirteen-coordinate actual-adjacency system on its own selected window. -/
theorem P13Node21PartXIEntry.actualAssignmentMissing
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {previous : VerifiedP13MultiScaleCurvaturePrefix ctx}
    (entry : P13Node21PartXIEntry ctx previous) :
    ∀ state, (p13ActualAttachmentSystem ctx entry.window.1).value state ≠
      entry.fork.residual.assignment :=
  p13ActualAttachmentColdFork_missing entry.fork

/-- The retained selected window is exactly the one used by the Part-XI
continuation. -/
theorem P13Node21PartXIEntry.sameWindow
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {previous : VerifiedP13MultiScaleCurvaturePrefix ctx}
    (entry : P13Node21PartXIEntry ctx previous) :
    entry.fork.selectedWindow = entry.window :=
  p13ActualAttachmentColdFork_same_selected_window entry.fork

/-- Execute the same-context route on every actual member of the CT12-selected
packing.  This maps the supplied packing list; it does not enumerate graphs,
completions, or outside contexts. -/
noncomputable def p13Node21PartXIRoutes
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedP13MultiScaleCurvaturePrefix ctx) :
    List (P13Node21PartXIEntry ctx previous) :=
  (p13Windows ctx).attach.map
    (p13Node21PartXIEntry ctx previous)

/-- Exactly one route entry is produced for every packed window. -/
theorem p13Node21PartXIRoutes_length
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedP13MultiScaleCurvaturePrefix ctx) :
    (p13Node21PartXIRoutes ctx previous).length = p13 ctx := by
  rw [p13Node21PartXIRoutes, List.length_map, List.length_attach]
  simp [p13Windows, p13,
    Graph.InducedPathPacking.packingNumber,
    Graph.InducedPathPacking.windows]

/-- The four honest constructors of the graph-owned Part-XI frontier. -/
inductive P13PartXIOutcomeTag
  | surplus
  | dyadic
  | corridorHigh
  | quiet
  deriving DecidableEq

/-- Read the constructor already computed for one exact route entry. -/
def P13Node21PartXIEntry.outcomeTag
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {previous : VerifiedP13MultiScaleCurvaturePrefix ctx}
    (entry : P13Node21PartXIEntry ctx previous) : P13PartXIOutcomeTag :=
  match entry.frontier with
  | .surplus .. => .surplus
  | .dyadicTargetHit .. => .dyadic
  | .corridorHighDegree .. => .corridorHigh
  | .quiet .. => .quiet

/-- Exact subledger of entries with one computed structural constructor. -/
noncomputable def p13Node21PartXIRoutesWithTag
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedP13MultiScaleCurvaturePrefix ctx)
    (tag : P13PartXIOutcomeTag) : List (P13Node21PartXIEntry ctx previous) :=
  (p13Node21PartXIRoutes ctx previous).filter fun entry =>
    entry.outcomeTag = tag

private theorem fourTagPartitionLength
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {previous : VerifiedP13MultiScaleCurvaturePrefix ctx}
    (entries : List (P13Node21PartXIEntry ctx previous)) :
    (entries.filter fun entry =>
        entry.outcomeTag = P13PartXIOutcomeTag.surplus).length +
      (entries.filter fun entry =>
        entry.outcomeTag = P13PartXIOutcomeTag.dyadic).length +
      (entries.filter fun entry =>
        entry.outcomeTag = P13PartXIOutcomeTag.corridorHigh).length +
      (entries.filter fun entry =>
        entry.outcomeTag = P13PartXIOutcomeTag.quiet).length = entries.length := by
  induction entries with
  | nil => rfl
  | cons entry tail ih =>
      cases tagEquation : entry.outcomeTag <;>
        simp [tagEquation] <;> omega

/-- Every packed window occurs in exactly one of the four same-context
structural ledgers.  This is a routing theorem only; it assigns no entropy or
density payment to any constructor. -/
theorem p13Node21PartXIRoutes_partition
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (previous : VerifiedP13MultiScaleCurvaturePrefix ctx) :
    (p13Node21PartXIRoutesWithTag ctx previous .surplus).length +
      (p13Node21PartXIRoutesWithTag ctx previous .dyadic).length +
      (p13Node21PartXIRoutesWithTag ctx previous .corridorHigh).length +
      (p13Node21PartXIRoutesWithTag ctx previous .quiet).length = p13 ctx := by
  rw [p13Node21PartXIRoutesWithTag, p13Node21PartXIRoutesWithTag,
    p13Node21PartXIRoutesWithTag, p13Node21PartXIRoutesWithTag,
    fourTagPartitionLength, p13Node21PartXIRoutes_length]

end Erdos64EG.Internal
