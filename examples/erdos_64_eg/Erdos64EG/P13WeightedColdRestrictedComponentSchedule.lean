import Erdos64EG.P13WeightedColdRestrictedEntries
import StructuralExhaustion.Graph.FiniteLexFirstSimplePath
import StructuralExhaustion.Graph.InducedPathRestrictedComponentBoundarySchedule

namespace Erdos64EG.Internal

open StructuralExhaustion
open StructuralExhaustion.Graph
open StructuralExhaustion.Graph.InducedPathWindowLedger

universe u

variable {ctx : Core.MinimalCounterexampleContext
  PackedProblem.{u} PackedTarget.{u}}
variable {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}

noncomputable abbrev P13ColdFamily :=
  p13WeightedColdWindowFamily (ctx := ctx) (node21 := node21)

noncomputable abbrev P13RestrictedComponentInput :=
  InducedPathRestrictedComponentBoundarySchedule.Input
    (P13ColdFamily (ctx := ctx) (node21 := node21))

/-- Construct the restricted component input from the literal component-boundary
constructor and the already proved all-darts non-bridge theorem. -/
noncomputable def p13RestrictedComponentInputOfBoundary
    (entry : P13WeightedColdRestrictedEntry ctx node21)
    (boundary : InducedPathRestrictedColdSkeleton.BoundaryStub
      (P13ColdFamily (ctx := ctx) (node21 := node21)))
    (tokenExact : boundary.token = entry.source.2.stub.token) :
    P13RestrictedComponentInput (ctx := ctx) (node21 := node21) := by
  refine { anchor := boundary, notBridge := ?_ }
  have sourceNotBridge :=
    (p13SelectedWindowCorridorProducer ctx).notBridge entry.source.2.stub.dart
  have edgeExact :
      (InducedPathColdCorridor.CubicStub.dart
        { token := boundary.token, cubic := boundary.cubic }).edge =
      entry.source.2.stub.dart.edge := by
    change s(selectedWindow ctx.G.object boundary.token.1 boundary.token.2.1,
        boundary.token.2.2.1) =
      s(selectedWindow ctx.G.object entry.source.2.stub.token.1
          entry.source.2.stub.token.2.1,
        entry.source.2.stub.token.2.2.1)
    rw [tokenExact]
  rw [edgeExact]
  exact sourceNotBridge

/-- Exact scheduled output.  The component constructor stores the restricted
input; its successor and path are then computed canonically by the graph
layer.  The cross-window constructor is retained unchanged. -/
inductive P13WeightedColdRestrictedScheduledResult
    (entry : P13WeightedColdRestrictedEntry ctx node21) where
  | component
      (boundary : InducedPathRestrictedColdSkeleton.BoundaryStub
        (P13ColdFamily (ctx := ctx) (node21 := node21)))
      (tokenExact : boundary.token = entry.source.2.stub.token)
      (routeExact : entry.route = .componentBoundary boundary tokenExact)
      (input : P13RestrictedComponentInput (ctx := ctx) (node21 := node21))
      (inputExact : input =
        p13RestrictedComponentInputOfBoundary entry boundary tokenExact)
  | crossWindow
      (residual : InducedPathRestrictedColdSkeleton.CrossWindowResidual
        (P13ColdFamily (ctx := ctx) (node21 := node21)) entry.source.2.stub)
      (routeExact : entry.route = .crossWindow residual)

noncomputable def p13ScheduleRestrictedEntry
    (entry : P13WeightedColdRestrictedEntry ctx node21) :
    P13WeightedColdRestrictedScheduledResult entry := by
  cases routeEquation : entry.route with
  | componentBoundary boundary tokenExact =>
      exact .component boundary tokenExact routeEquation
        (p13RestrictedComponentInputOfBoundary entry boundary tokenExact) rfl
  | crossWindow residual => exact .crossWindow residual routeEquation

/-- One scheduled result for every exact C153.1a entry, in the same order. -/
noncomputable def p13WeightedColdRestrictedComponentSchedule :=
  (p13WeightedColdRestrictedEntries
    (ctx := ctx) (node21 := node21)).attach.map fun entry =>
      Sigma.mk entry.1 (p13ScheduleRestrictedEntry entry.1)

theorem p13WeightedColdRestrictedComponentSchedule_length :
    (p13WeightedColdRestrictedComponentSchedule
      (ctx := ctx) (node21 := node21)).length =
      (p13WeightedColdRestrictedEntries
        (ctx := ctx) (node21 := node21)).length := by
  simp [p13WeightedColdRestrictedComponentSchedule]

/-- The complete node-`[153]` entry classifier retains exactly the original
node-`[152]` source order.  Both original constructors are included: a
component entry is expanded to its canonical input, while a cross-window
entry is retained unchanged. -/
theorem p13WeightedColdRestrictedComponentSchedule_sources :
    (p13WeightedColdRestrictedComponentSchedule
      (ctx := ctx) (node21 := node21)).map
        (fun scheduled => scheduled.1.source) =
      p13WeightedColdBranchExcessSchedule
        (ctx := ctx) (node21 := node21) := by
  let entries := p13WeightedColdRestrictedEntries
    (ctx := ctx) (node21 := node21)
  have attachSources :
      (entries.attach.map fun entry =>
          Sigma.mk entry.1 (p13ScheduleRestrictedEntry entry.1)).map
          (fun scheduled => scheduled.1.source) =
        entries.map P13WeightedColdRestrictedEntry.source := by
    induction entries with
    | nil => rfl
    | cons head tail ih => simp_all
  simpa [p13WeightedColdRestrictedComponentSchedule, entries] using
    attachSources.trans
      (p13WeightedColdRestrictedEntries_sources
        (ctx := ctx) (node21 := node21))

/-- Every exact selected branch-excess half-edge therefore occurs once on the
existing `[152] -> [153]` schedule. -/
theorem p13WeightedColdRestrictedComponentSchedule_sources_nodup :
    ((p13WeightedColdRestrictedComponentSchedule
      (ctx := ctx) (node21 := node21)).map
        (fun scheduled => scheduled.1.source)).Nodup := by
  rw [p13WeightedColdRestrictedComponentSchedule_sources]
  exact p13WeightedColdBranchExcessSchedule_nodup

/-- The component constructor exposes the paper's exact structural corridor:
same source token, distinct cyclic successor in the same restricted component,
and the canonical declared-order BFS shortest path. -/
theorem restricted_component_payload
    (entry : P13WeightedColdRestrictedEntry ctx node21)
    (boundary : InducedPathRestrictedColdSkeleton.BoundaryStub
      (P13ColdFamily (ctx := ctx) (node21 := node21)))
    (tokenExact : boundary.token = entry.source.2.stub.token)
    (_routeExact : entry.route = .componentBoundary boundary tokenExact)
    (input : P13RestrictedComponentInput (ctx := ctx) (node21 := node21))
    (inputExact : input =
      p13RestrictedComponentInputOfBoundary entry boundary tokenExact) :
    input.anchor.token = entry.source.2.stub.token ∧
      (InducedPathRestrictedComponentBoundarySchedule.successor input ≠
        input.anchor) ∧
      InducedPathRestrictedColdSkeleton.component
          (InducedPathRestrictedComponentBoundarySchedule.successor input) =
        InducedPathRestrictedColdSkeleton.component input.anchor ∧
      (InducedPathRestrictedComponentBoundarySchedule.componentPath input).IsPath ∧
      (InducedPathRestrictedComponentBoundarySchedule.componentPath input).length =
        (InducedPathRestrictedColdSkeleton.component input.anchor).toSimpleGraph.dist
          (InducedPathRestrictedComponentBoundarySchedule.twoStubComponent input).componentRoot
          (InducedPathRestrictedComponentBoundarySchedule.twoStubComponent input).componentTarget := by
  subst input
  exact ⟨tokenExact,
    InducedPathRestrictedComponentBoundarySchedule.successor_distinct _,
    InducedPathRestrictedComponentBoundarySchedule.successor_same_component _,
    InducedPathRestrictedComponentBoundarySchedule.componentPath_isPath _,
    InducedPathRestrictedComponentBoundarySchedule.componentPath_shortest _⟩

/-- The currently verified existing-edge component payload: the actual restricted
outside component, literal cyclic successor, and declared-order
lexicographically selected shortest return path are all computed from the
same source entry. -/
theorem restricted_component_declaredOrderCorridor
    (entry : P13WeightedColdRestrictedEntry ctx node21)
    (boundary : InducedPathRestrictedColdSkeleton.BoundaryStub
      (P13ColdFamily (ctx := ctx) (node21 := node21)))
    (tokenExact : boundary.token = entry.source.2.stub.token)
    (_routeExact : entry.route = .componentBoundary boundary tokenExact)
    (input : P13RestrictedComponentInput (ctx := ctx) (node21 := node21))
    (inputExact : input =
      p13RestrictedComponentInputOfBoundary entry boundary tokenExact) :
    (∀ vertex,
      vertex ∈ InducedPathRestrictedComponentBoundarySchedule.componentVertices input ↔
        (InducedPathRestrictedColdSkeleton.outsideObject
          (P13ColdFamily (ctx := ctx) (node21 := node21))).graph.connectedComponentMk
            vertex = InducedPathRestrictedColdSkeleton.component input.anchor) ∧
      InducedPathRestrictedComponentBoundarySchedule.successor input =
        @List.next _
          (InducedPathRestrictedComponentBoundarySchedule.boundaryStubs
            (P13ColdFamily (ctx := ctx) (node21 := node21))).decEq
          (InducedPathRestrictedComponentBoundarySchedule.incidentStubs input)
          input.anchor
          (InducedPathRestrictedComponentBoundarySchedule.anchor_mem_incidentStubs input) ∧
      (InducedPathRestrictedComponentBoundarySchedule.componentPathDeclaredOrderCertificate
        input).path =
        InducedPathRestrictedComponentBoundarySchedule.componentPath input := by
  subst input
  exact ⟨InducedPathRestrictedComponentBoundarySchedule.mem_componentVertices_iff _,
    rfl,
    InducedPathRestrictedComponentBoundarySchedule.componentPathDeclaredOrderCertificate_path _⟩

/-- Local work certificate for every computed component path. -/
theorem restricted_component_path_support_bound
    (entry : P13WeightedColdRestrictedEntry ctx node21)
    (boundary : InducedPathRestrictedColdSkeleton.BoundaryStub
      (P13ColdFamily (ctx := ctx) (node21 := node21)))
    (tokenExact : boundary.token = entry.source.2.stub.token)
    (input : P13RestrictedComponentInput (ctx := ctx) (node21 := node21))
    (inputExact : input =
      p13RestrictedComponentInputOfBoundary entry boundary tokenExact) :
    (InducedPathRestrictedComponentBoundarySchedule.componentPath input).support.length ≤
      (InducedPathRestrictedComponentBoundarySchedule.componentObject input).input.vertices.card := by
  subst input
  exact InducedPathRestrictedComponentBoundarySchedule.componentPath_support_length_le_component _

/-!
## Manuscript lexicographically first corridor

The declared-order BFS corridor above remains useful for the existing local
schedule, but the original manuscript chooses the lexicographically first
*simple* endpoint path.  The following is a thin specialization of the graph
framework selector to the very same restricted component, source, and literal
cyclic successor.  It introduces no new outcome: only the payload of the
existing `component` constructor is strengthened.
-/

/-- The generic lex-first selector instantiated on the actual restricted
outside component carried by the node-`[153]` component constructor. -/
noncomputable def p13RestrictedLexFirstCorridorProfile
    (input : P13RestrictedComponentInput (ctx := ctx) (node21 := node21)) :
    FiniteLexFirstSimplePath.Profile
      (InducedPathRestrictedComponentBoundarySchedule.componentObject input) where
  source :=
    (InducedPathRestrictedComponentBoundarySchedule.twoStubComponent input).componentRoot
  target :=
    (InducedPathRestrictedComponentBoundarySchedule.twoStubComponent input).componentTarget
  reachable :=
    (InducedPathRestrictedComponentBoundarySchedule.twoStubComponent input).component_preconnected
      _ _

/-- The paper's corridor: the lexicographically first simple path from the
anchor's outside endpoint to the true cyclic successor's outside endpoint,
inside the actual restricted component. -/
noncomputable def p13RestrictedLexFirstCorridor
    (input : P13RestrictedComponentInput (ctx := ctx) (node21 := node21)) :=
  (p13RestrictedLexFirstCorridorProfile input).firstPath

/-- Exact endpoint, simplicity, minimality, and local carrier bound for the
paper's selected corridor on the existing component outcome. -/
theorem restricted_component_lexFirstCorridor
    (entry : P13WeightedColdRestrictedEntry ctx node21)
    (boundary : InducedPathRestrictedColdSkeleton.BoundaryStub
      (P13ColdFamily (ctx := ctx) (node21 := node21)))
    (tokenExact : boundary.token = entry.source.2.stub.token)
    (_routeExact : entry.route = .componentBoundary boundary tokenExact)
    (input : P13RestrictedComponentInput (ctx := ctx) (node21 := node21))
    (inputExact : input =
      p13RestrictedComponentInputOfBoundary entry boundary tokenExact) :
    input.anchor.token = entry.source.2.stub.token ∧
      (InducedPathRestrictedComponentBoundarySchedule.successor input ≠
        input.anchor) ∧
      InducedPathRestrictedColdSkeleton.component
          (InducedPathRestrictedComponentBoundarySchedule.successor input) =
        InducedPathRestrictedColdSkeleton.component input.anchor ∧
      (p13RestrictedLexFirstCorridor input).1.IsPath ∧
      (p13RestrictedLexFirstCorridor input).1.support.head? =
        some
          (InducedPathRestrictedComponentBoundarySchedule.twoStubComponent
            input).componentRoot ∧
      (p13RestrictedLexFirstCorridor input).1.support.getLast? =
        some
          (InducedPathRestrictedComponentBoundarySchedule.twoStubComponent
            input).componentTarget ∧
      (∀ path :
          (InducedPathRestrictedComponentBoundarySchedule.componentObject input).graph.Path
            (InducedPathRestrictedComponentBoundarySchedule.twoStubComponent
              input).componentRoot
            (InducedPathRestrictedComponentBoundarySchedule.twoStubComponent
              input).componentTarget,
        ¬(p13RestrictedLexFirstCorridorProfile input).code path <
          (p13RestrictedLexFirstCorridorProfile input).code
            (p13RestrictedLexFirstCorridor input)) ∧
      (p13RestrictedLexFirstCorridor input).1.length <
        (InducedPathRestrictedComponentBoundarySchedule.componentObject
          input).input.vertices.card := by
  subst input
  exact ⟨tokenExact,
    InducedPathRestrictedComponentBoundarySchedule.successor_distinct _,
    InducedPathRestrictedComponentBoundarySchedule.successor_same_component _,
    (p13RestrictedLexFirstCorridorProfile _).firstPath_isPath,
    (p13RestrictedLexFirstCorridorProfile _).firstPath_head,
    (p13RestrictedLexFirstCorridorProfile _).firstPath_getLast,
    (p13RestrictedLexFirstCorridorProfile _).no_earlier_path,
    (p13RestrictedLexFirstCorridorProfile _).firstPath_length_lt⟩

end Erdos64EG.Internal
