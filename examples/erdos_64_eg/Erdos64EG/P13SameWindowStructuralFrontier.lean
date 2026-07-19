import Erdos64EG.P13ActualAttachmentColdFork
import Erdos64EG.P13SelectedWindowCorridor
import Mathlib.Tactic

namespace Erdos64EG.Internal

open StructuralExhaustion
open StructuralExhaustion.Graph
open StructuralExhaustion.Graph.InducedPathWindowLedger

universe u

/-!
# Node [159]: same-window structural frontier

This is the thin continuation of the parallel node-[158] actual-attachment
cold fork.  It executes the existing graph-owned selected-window corridor and
flattens its result to the four honest structural outcomes used at the next
frontier: a surplus position in the selected window, a dyadic target hit, a
first high-degree corridor event, or a quiet `ColdStructuralGerm`.

The quiet output is deliberately not promoted to a bounded germ.  This module
contains no density statement.  The separate 91-coordinate realization
obligation is reserved for node `[160]` and is not consumed here.
-/

variable {ctx : Core.MinimalCounterexampleContext
  PackedProblem.{u} PackedTarget.{u}}
variable {previous : VerifiedP13MultiScaleCurvaturePrefix ctx}
variable {window : P13ActualSelectedWindow ctx}

private noncomputable abbrev CorridorProfile
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :=
  InducedPathColdCorridor.firstFailureProfile
    (p13SelectedWindowCorridorProducer ctx)
    PowerOfTwoLength powerOfTwoLengthDecidable

private noncomputable abbrev CorridorFirstHit
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (stub : InducedPathColdCorridor.CubicStub ctx.G.object) :=
  Core.FiniteSearch.FirstHit
    ((CorridorProfile ctx).stages stub).values
    ((CorridorProfile ctx).Event stub)

/-- Exact four-way graph-owned continuation of one node-[158] cold fork.
The result is indexed by the fork itself, so it cannot be constructed as this
node's execution output without retaining the exact predecessor and selected
window. -/
inductive P13SameWindowStructuralFrontier
    (fork : P13ActualAttachmentColdFork ctx previous window) where
  | surplus
      (position : Fin 13)
      (high : 3 < ctx.G.object.degree (window.1 position))
  | dyadicTargetHit
      (stub : InducedPathColdCorridor.CubicStub ctx.G.object)
      (sameWindow : stub.window = selectedConnectorWindowIndex window)
      (hit : CorridorFirstHit ctx stub)
      (targetProof : InducedPathColdCorridor.F1
        (p13SelectedWindowCorridorProducer ctx) PowerOfTwoLength
        stub hit.value)
      (target : InducedPathColdCorridor.Producer.TargetHit
        (p13SelectedWindowCorridorProducer ctx) PowerOfTwoLength)
      (targetExact : target = InducedPathColdCorridor.targetHitOfF1
        (p13SelectedWindowCorridorProducer ctx) PowerOfTwoLength
        stub hit.value targetProof)
  | corridorHighDegree
      (stub : InducedPathColdCorridor.CubicStub ctx.G.object)
      (sameWindow : stub.window = selectedConnectorWindowIndex window)
      (hit : CorridorFirstHit ctx stub)
      (noEarlierTarget : ¬InducedPathColdCorridor.F1
        (p13SelectedWindowCorridorProducer ctx) PowerOfTwoLength
        stub hit.value)
      (high : InducedPathColdCorridor.F4 stub hit.value)
      (handoff : InducedPathColdCorridor.Producer.SurplusHandoff
        (p13SelectedWindowCorridorProducer ctx))
      (handoffExact : handoff = InducedPathColdCorridor.surplusHandoffOfF4
        (p13SelectedWindowCorridorProducer ctx) stub hit.value high)
  | quiet
      (stub : InducedPathColdCorridor.CubicStub ctx.G.object)
      (sameWindow : stub.window = selectedConnectorWindowIndex window)
      (noEvent : ∀ stage, stage ∈ ((CorridorProfile ctx).stages stub).values →
        ¬(CorridorProfile ctx).Event stub stage)
      (germ : InducedPathColdCorridor.Producer.ColdStructuralGerm
        (p13SelectedWindowCorridorProducer ctx) PowerOfTwoLength stub)

/-- Execute node `[159]`.  The sole branch source is
`routeSelectedWindowCorridor`; no route result, stub, hit, or germ is accepted
from the caller. -/
noncomputable def runP13SameWindowStructuralFrontier
    (fork : P13ActualAttachmentColdFork ctx previous window) :
    P13SameWindowStructuralFrontier fork :=
  match routeSelectedWindowCorridor ctx window with
  | .surplus position high => .surplus position high
  | .corridor stub sameWindow result =>
      match result with
      | .germ noEvent germ => .quiet stub sameWindow noEvent germ
      | .first hit event =>
          match event with
          | .f1 targetProof _target =>
              .dyadicTargetHit stub sameWindow hit targetProof
                (InducedPathColdCorridor.targetHitOfF1
                  (p13SelectedWindowCorridorProducer ctx) PowerOfTwoLength
                  stub hit.value targetProof) rfl
          | .f2 _noF1 _proof impossible => impossible.elim
          | .f3 _noF1 _noF2 _proof impossible => impossible.elim
          | .f4 noF1 _noF2 _noF3 high _handoff =>
              .corridorHighDegree stub sameWindow hit noF1 high
                (InducedPathColdCorridor.surplusHandoffOfF4
                  (p13SelectedWindowCorridorProducer ctx)
                  stub hit.value high) rfl

/-- The four constructors exhaust the computed continuation. -/
theorem runP13SameWindowStructuralFrontier_exhaustive
    (fork : P13ActualAttachmentColdFork ctx previous window) :
    (∃ position high,
      runP13SameWindowStructuralFrontier fork = .surplus position high) ∨
    (∃ stub same hit targetProof target targetExact,
      runP13SameWindowStructuralFrontier fork =
        .dyadicTargetHit stub same hit targetProof target targetExact) ∨
    (∃ stub same hit noTarget high handoff handoffExact,
      runP13SameWindowStructuralFrontier fork =
        .corridorHighDegree stub same hit noTarget high handoff handoffExact) ∨
    (∃ stub same noEvent germ,
      runP13SameWindowStructuralFrontier fork =
        .quiet stub same noEvent germ) := by
  cases equation : runP13SameWindowStructuralFrontier fork with
  | surplus position high => exact Or.inl ⟨position, high, rfl⟩
  | dyadicTargetHit stub same hit targetProof target targetExact =>
      exact Or.inr (Or.inl
        ⟨stub, same, hit, targetProof, target, targetExact, rfl⟩)
  | corridorHighDegree stub same hit noTarget high handoff handoffExact =>
      exact Or.inr (Or.inr (Or.inl
        ⟨stub, same, hit, noTarget, high, handoff, handoffExact, rfl⟩))
  | quiet stub same noEvent germ =>
      exact Or.inr (Or.inr (Or.inr ⟨stub, same, noEvent, germ, rfl⟩))

/-- A dyadic constructor contains a literal target cycle rooted at the exact
canonical stub selected for the incoming window. -/
theorem P13SameWindowStructuralFrontier.dyadic_target_same_stub
    {_fork : P13ActualAttachmentColdFork ctx previous window}
    {stub : InducedPathColdCorridor.CubicStub ctx.G.object}
    {_same : stub.window = selectedConnectorWindowIndex window}
    {hit : CorridorFirstHit ctx stub}
    {targetProof : InducedPathColdCorridor.F1
      (p13SelectedWindowCorridorProducer ctx) PowerOfTwoLength
      stub hit.value}
    {target : InducedPathColdCorridor.Producer.TargetHit
      (p13SelectedWindowCorridorProducer ctx) PowerOfTwoLength}
    (targetExact : target = InducedPathColdCorridor.targetHitOfF1
      (p13SelectedWindowCorridorProducer ctx) PowerOfTwoLength
      stub hit.value targetProof) :
    target.stub = stub := by
  rw [targetExact]
  rfl

/-- A corridor-high constructor is the handoff built from the exact first
high stage of the same canonical stub. -/
theorem P13SameWindowStructuralFrontier.high_handoff_same_stub
    {_fork : P13ActualAttachmentColdFork ctx previous window}
    {stub : InducedPathColdCorridor.CubicStub ctx.G.object}
    {_same : stub.window = selectedConnectorWindowIndex window}
    {hit : CorridorFirstHit ctx stub}
    {_noTarget : ¬InducedPathColdCorridor.F1
      (p13SelectedWindowCorridorProducer ctx) PowerOfTwoLength
      stub hit.value}
    {high : InducedPathColdCorridor.F4 stub hit.value}
    {handoff : InducedPathColdCorridor.Producer.SurplusHandoff
      (p13SelectedWindowCorridorProducer ctx)}
    (handoffExact : handoff = InducedPathColdCorridor.surplusHandoffOfF4
      (p13SelectedWindowCorridorProducer ctx) stub hit.value high) :
    handoff.stub = stub := by
  rw [handoffExact]
  rfl

/-- The first-hit value in the dyadic branch retains the framework's exact
clean prefix. -/
theorem P13SameWindowStructuralFrontier.dyadic_prefix_clear
    {_fork : P13ActualAttachmentColdFork ctx previous window}
    {stub : InducedPathColdCorridor.CubicStub ctx.G.object}
    {_same : stub.window = selectedConnectorWindowIndex window}
    {hit : CorridorFirstHit ctx stub}
    {targetProof : InducedPathColdCorridor.F1
      (p13SelectedWindowCorridorProducer ctx) PowerOfTwoLength
      stub hit.value}
    {target : InducedPathColdCorridor.Producer.TargetHit
      (p13SelectedWindowCorridorProducer ctx) PowerOfTwoLength}
    (_targetExact : target = InducedPathColdCorridor.targetHitOfF1
      (p13SelectedWindowCorridorProducer ctx) PowerOfTwoLength
      stub hit.value targetProof) :
    ∀ stage, stage ∈ hit.before → ¬(CorridorProfile ctx).Event stub stage :=
  hit.beforeAbsent

/-- Exact number of event checks used to verify one already constructed,
proof-carrying return certificate. -/
noncomputable def p13CorridorCertificateChecks
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (stub : InducedPathColdCorridor.CubicStub ctx.G.object) : Nat :=
  ((CorridorProfile ctx).stages stub).values.length

theorem p13CorridorCertificateChecks_le_vertices
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (stub : InducedPathColdCorridor.CubicStub ctx.G.object) :
    p13CorridorCertificateChecks ctx stub ≤
      ctx.G.object.input.vertices.card := by
  change ((p13SelectedWindowCorridorProducer ctx).ambientReturn stub).support.length ≤
    ctx.G.object.input.vertices.card
  simpa only [FinEnum.orderedValues_length] using
    Core.Enumeration.length_le_elems_of_nodup
      ctx.G.object.input.vertices
      (((p13SelectedWindowCorridorProducer ctx).ambientReturn_isPath
        stub).support_nodup)

/-- Visible local scan budget.  It counts two possible scans of the thirteen
window positions, one scan of the existing external-incidence token schedule,
and verification of one proof-carrying return certificate at at most `n`
stages.  It does not claim a constructive path-search runtime for
`DartReturn.ofNotBridge`. -/
noncomputable def p13SameWindowStructuralVisibleChecks
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    Nat :=
  26 + (tokens ctx.G.object).card + ctx.G.object.input.vertices.card

theorem p13SameWindowStructuralVisibleChecks_eq
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}) :
    p13SameWindowStructuralVisibleChecks ctx =
      26 + (15 * packingNumber ctx.G.object + windowSurplus ctx.G.object) +
        ctx.G.object.input.vertices.card := by
  rw [p13SameWindowStructuralVisibleChecks,
    tokens_card_eq_fifteen_mul_packing_add_surplus ctx.G.object
      (fun vertex =>
        ctx.baseline.trans (ctx.G.object.minDegree_le_degree vertex))]

end Erdos64EG.Internal
