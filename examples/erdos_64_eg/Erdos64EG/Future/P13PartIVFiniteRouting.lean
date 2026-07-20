import Erdos64EG.Future.P13ActualAttachmentResponse
import Erdos64EG.Future.P13HotColdInterface
import Erdos64EG.Future.P13MultiScaleConnectorState
import Erdos64EG.Future.P13LargeBudgetNetDeficiency
import StructuralExhaustion.Core.FiniteEntropyRankRouting
import StructuralExhaustion.Core.FiniteCodeCollision

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# Honest finite routing interface for Part IV

The only Boolean system used here is the graph-owned attachment system of one
actual selected window.  Its states are ambient vertices outside that window;
no family of graphs or completion oracle is accepted.  The generic runner
returns realization-backed entropy, exact response repetition with the
already verified quotient-rank payload, or a cold nonrepetitive residual.

The separate 91-barrier connector semantics cannot enter the entropy
constructor: target avoidance makes every retained flat connector bit true.
That fact is recorded below as an explicit bypass to the large-budget side.
-/

/-- Exact sequential collision of two actual outside vertices with the same
thirteen attachment bits.  The inherited state list is duplicate-free, so a
collision always contains two distinct vertices. -/
noncomputable def P13ActualAttachmentRepetitive
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (window : SelectedP13Window ctx) : Prop :=
  Nonempty (Core.FiniteCodeCollision.OrderedCollision
    (p13ActualAttachmentSystem ctx window.1).value
    (p13ActualAttachmentStates ctx window.1).orderedValues)

/-- Complete Boolean realization is impossible even for the strongest
graph-owned attachment system presently available.  The all-true assignment
would attach one outside vertex at path positions `0` and `2`, producing the
forbidden length-four cycle certified by the node-`[18]` legality theorem. -/
theorem p13ActualAttachment_hot_impossible
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx)
    (window : SelectedP13Window ctx)
    (certificate :
      (p13ActualAttachmentSystem ctx window.1).HotCertificate) : False := by
  let assignment : Fin 13 → Bool := fun _position => true
  obtain ⟨state, realized⟩ := certificate.realizes assignment
  have atZero :
      (p13ActualAttachmentSystem ctx window.1).value state (0 : Fin 13) =
        true := by
    rw [realized]
  have atTwo :
      (p13ActualAttachmentSystem ctx window.1).value state (2 : Fin 13) =
        true := by
    rw [realized]
  have memberZero :
      (0 : Fin 13) ∈ packedStaticInput.inducedPathAttachmentLabel
        13 ctx window.1 state.1 :=
    (p13ActualAttachmentSystem_value_iff_labelMembership
      ctx window.1 state (0 : Fin 13)).1 atZero
  have memberTwo :
      (2 : Fin 13) ∈ packedStaticInput.inducedPathAttachmentLabel
        13 ctx window.1 state.1 :=
    (p13ActualAttachmentSystem_value_iff_labelMembership
      ctx window.1 state (2 : Fin 13)).1 atTwo
  have legal := p13AttachmentLabel_legal ctx
    node21.previous.previous.residual window.1 state.1 state.2
    ⟨0, (p13ActualAttachmentSystem_value_eq_true_iff
      ctx window.1 state (0 : Fin 13)).1 atZero⟩
  exact (legal.2 (0 : Fin 13) memberZero (2 : Fin 13) memberTwo (by decide))
    ((pairCycleLength_powerOfTwo_iff_gap_two_or_six
      (0 : Fin 13) (2 : Fin 13) (by decide)).2 (Or.inl (by decide)))

@[implicit_reducible]
noncomputable def p13ActualAttachmentResponseCodes
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (window : SelectedP13Window ctx) : FinEnum (Fin 13 → Bool) := by
  letI : FinEnum (Fin 13) := inferInstance
  letI : FinEnum Bool := Core.Enumeration.bool
  infer_instance

/-- Sequential first-collision scan; it does not materialize the quadratic
dependent pair product. -/
noncomputable def p13ActualAttachmentRepetitionDecision
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (window : SelectedP13Window ctx) :=
  Core.FiniteCodeCollision.decide
    (p13ActualAttachmentResponseCodes ctx window)
    (p13ActualAttachmentSystem ctx window.1).value
    (p13ActualAttachmentStates ctx window.1).orderedValues

/-- Finite decision over actual outside vertices and thirteen Boolean
coordinates. -/
noncomputable def p13ActualAttachmentRepetitiveDecidable
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (window : SelectedP13Window ctx) :
    Decidable (P13ActualAttachmentRepetitive ctx window) :=
  match p13ActualAttachmentRepetitionDecision ctx window with
  | .collision collision => isTrue ⟨collision⟩
  | .unique codesNodup => isFalse fun ⟨collision⟩ =>
      collision.false_of_codes_nodup codesNodup

/-- The rank payload on the repetitive branch is deliberately only the
existing CT15 quotient-rank equality.  It is not promoted to Boolean entropy. -/
structure P13RepetitiveQuotientRankPayload
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (window : SelectedP13Window ctx) : Type u where
  repetitive : P13ActualAttachmentRepetitive ctx window
  quotientFullRank :
    (p13CurvatureResponseProfile ctx).ct15Profile.coordinates.card =
      (p13RemainderCurvatureProfile ctx).wedgeCount

/-- Concrete three-way profile on the actual graph and the same-context
node-`[21]`/node-`[47]` predecessor. -/
noncomputable def p13PartIVWindowProfile
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    {coverage : P13CoverageResidual ctx
      (p13MultiScalePackingPrefix node21)}
    (joined : P13DensityConnectedGlobalRankPrefix ctx node21 coverage)
    (window : SelectedP13Window ctx) :
    Core.FiniteEntropyRankRouting.Profile where
  system := p13ActualAttachmentSystem ctx window.1
  Repetitive := P13ActualAttachmentRepetitive ctx window
  repetitiveDecidable := p13ActualAttachmentRepetitiveDecidable ctx window
  RankPayload := P13RepetitiveQuotientRankPayload ctx window
  rankOfRepetitive := fun repetitive =>
    ⟨repetitive, densityConnected_fullRankCount joined⟩

/-- Computed local route.  No author-selected branch tag occurs. -/
noncomputable def runP13PartIVWindowRoute
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    {coverage : P13CoverageResidual ctx
      (p13MultiScalePackingPrefix node21)}
    (joined : P13DensityConnectedGlobalRankPrefix ctx node21 coverage)
    (window : SelectedP13Window ctx) :
    (p13PartIVWindowProfile joined window).Outcome :=
  (p13PartIVWindowProfile joined window).run

/-- The computed actual-attachment route cannot take the entropy constructor:
its certificate would realize the forbidden all-true attachment pattern. -/
theorem runP13PartIVWindowRoute_not_entropy
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    {coverage : P13CoverageResidual ctx
      (p13MultiScalePackingPrefix node21)}
    (joined : P13DensityConnectedGlobalRankPrefix ctx node21 coverage)
    (window : SelectedP13Window ctx) :
    ¬∃ route, runP13PartIVWindowRoute joined window = .entropy route := by
  rintro ⟨route, _equal⟩
  exact p13ActualAttachment_hot_impossible node21 window route.certificate

/-- The exact executable outcome on actual attachment states after eliminating
the impossible entropy certificate.  Its type has precisely the repetitive
rank and cold nonrepetitive constructors, avoiding dependent constructor
equalities when this module is imported through the aggregate web target. -/
noncomputable def runP13PartIVWindowBypass
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    {coverage : P13CoverageResidual ctx
      (p13MultiScalePackingPrefix node21)}
    (joined : P13DensityConnectedGlobalRankPrefix ctx node21 coverage)
    (window : SelectedP13Window ctx) :
    (p13PartIVWindowProfile joined window).NonEntropyOutcome :=
  (p13PartIVWindowProfile joined window).runWithoutEntropy fun route =>
    p13ActualAttachment_hot_impossible node21 window route.certificate

/-- Same-context finite routing data over every exact CT12-selected window. -/
structure P13PartIVFiniteRouting
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx)
    (coverage : P13CoverageResidual ctx
      (p13MultiScalePackingPrefix node21)) where
  previous : P13DensityConnectedGlobalRankPrefix ctx node21 coverage

noncomputable def p13PartIVFiniteRouting
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    {coverage : P13CoverageResidual ctx
      (p13MultiScalePackingPrefix node21)}
    (joined : P13DensityConnectedGlobalRankPrefix ctx node21 coverage) :
    P13PartIVFiniteRouting ctx node21 coverage where
  previous := joined

/-- Execute the canonical route for one member of the retained finite window
schedule. -/
noncomputable def P13PartIVFiniteRouting.route
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    {coverage : P13CoverageResidual ctx
      (p13MultiScalePackingPrefix node21)}
    (routing : P13PartIVFiniteRouting ctx node21 coverage)
    (window : SelectedP13Window ctx) :
    (p13PartIVWindowProfile routing.previous window).Outcome :=
  runP13PartIVWindowRoute routing.previous window

/-- Exact reason the actual 91-barrier connector semantics bypasses node
`[48]`: even coordinatewise choices of unrelated literal connectors cannot
realize the Boolean cube. -/
structure P13ConnectorEntropyBypass
    (ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u})
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx)
    (coverage : P13CoverageResidual ctx
      (p13MultiScalePackingPrefix node21))
    (window : P13SelectedConnectorWindow ctx) where
  previous : P13DensityConnectedGlobalRankPrefix ctx node21 coverage
  noBooleanProduct : ¬P13CoordinatewiseFlatRealization ctx window

/-- Construct the honest large-budget bypass without an entropy premise. -/
def p13ConnectorEntropyBypass
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    {coverage : P13CoverageResidual ctx
      (p13MultiScalePackingPrefix node21)}
    (joined : P13DensityConnectedGlobalRankPrefix ctx node21 coverage)
    (window : P13SelectedConnectorWindow ctx) :
    P13ConnectorEntropyBypass ctx node21 coverage window where
  previous := joined
  noBooleanProduct := p13CoordinatewiseFlatRealization_impossible ctx window

/-- If the separately owed exact quarter budget is later proved, any honest
Part-IV routing value composes with the already verified node-`[56]` handoff.
No property of the entropy or rank tag is used to manufacture that budget. -/
def P13PartIVFiniteRouting.quarterHandoff
    {ctx : Core.MinimalCounterexampleContext PackedProblem.{u} PackedTarget.{u}}
    {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}
    {coverage : P13CoverageResidual ctx
      (p13MultiScalePackingPrefix node21)}
    (routing : P13PartIVFiniteRouting ctx node21 coverage)
    (budget : P13QuarterNetBudget ctx (node21 := node21) coverage) :
    P13QuarterNetDeficiencyHandoff ctx node21 coverage :=
  p13QuarterNetDeficiencyHandoff routing.previous budget

end Erdos64EG.Internal
