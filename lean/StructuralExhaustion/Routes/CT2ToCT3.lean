import StructuralExhaustion.CT2.State
import StructuralExhaustion.CT3.Capability

namespace StructuralExhaustion.Routes.CT2ToCT3

universe uResidual uPiece uSeed
universe uAmbient uBranch uCT2Piece uInterface uAbstract uContext uCandidate
universe uCT3Piece uCT3Context uCT3Candidate uRow

/-!
Canonical typed routing from CT2 separating-context residuals to CT3.

CT2 never imports CT3.  The route owns the only cross-tactic dependency,
discovers a problem-specific CT3 piece through a small typed capability, and
constructs the context-indexed target trigger from that seed.
-/

/-- Problem-specific discovery needed to interpret a semantic source as a
CT3 piece.  `Seed source` may be empty; disabled discovery therefore carries
an exact impossibility proof instead of a Boolean routing tag. -/
structure PieceDiscovery (Residual : Type uResidual) (Piece : Type uPiece) where
  Seed : Residual → Type uSeed
  discover : (source : Residual) → Core.Routing.Discovery (Seed source)
  piece : (source : Residual) → Seed source → Piece

/-- CT2's inherited branch is the CT3 route index. -/
def targetContext
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    {capability : CT2.Capability.{uAmbient, uBranch, uCT2Piece, uInterface,
      uAbstract, uContext, uCandidate} P Target}
    {ctx : Core.MinimalCounterexampleContext P Target}
    {input : CT2.Input capability ctx}
    (_source : CT2.SeparatingContextResidual capability ctx input) :
    Core.BranchContext P :=
  ctx.toBranchContext

/-- The framework route rule.  Discovery chooses only a typed seed; the rule
constructs the CT3 trigger and fixes its context definitionally. -/
def rule
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    {capability : CT2.Capability.{uAmbient, uBranch, uCT2Piece, uInterface,
      uAbstract, uContext, uCandidate} P Target}
    {ctx : Core.MinimalCounterexampleContext P Target}
    {input : CT2.Input capability ctx}
    {S : CT3.Spec.{uAmbient, uBranch, uCT3Piece, uCT3Context,
      uCT3Candidate, uRow} P}
    (targetCapability : CT3.Capability S)
    (sourceDiscovery : PieceDiscovery
      (CT2.SeparatingContextResidual capability ctx input) S.Piece) :
    Core.Routing.RouteRule
      (CT2.SeparatingContextResidual capability ctx input)
      targetCapability.tacticInterface where
  routeId := "CT2.residual.separatingContext->CT3"
  targetContext := targetContext
  Seed := sourceDiscovery.Seed
  discover := sourceDiscovery.discover
  buildTrigger := fun source seed => ⟨sourceDiscovery.piece source seed⟩

/-- Public trigger constructor.  Its dependent result prevents the route from
changing the inherited context. -/
def buildTrigger
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    {capability : CT2.Capability.{uAmbient, uBranch, uCT2Piece, uInterface,
      uAbstract, uContext, uCandidate} P Target}
    {ctx : Core.MinimalCounterexampleContext P Target}
    {input : CT2.Input capability ctx}
    {S : CT3.Spec.{uAmbient, uBranch, uCT3Piece, uCT3Context,
      uCT3Candidate, uRow} P}
    (targetCapability : CT3.Capability S)
    (sourceDiscovery : PieceDiscovery
      (CT2.SeparatingContextResidual capability ctx input) S.Piece)
    (source : CT2.SeparatingContextResidual capability ctx input)
    (seed : (rule targetCapability sourceDiscovery).Seed source) :
    CT3.Trigger S (targetContext source) :=
  (rule targetCapability sourceDiscovery).buildTrigger source seed

theorem branchContext_preserved
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    {capability : CT2.Capability.{uAmbient, uBranch, uCT2Piece, uInterface,
      uAbstract, uContext, uCandidate} P Target}
    {ctx : Core.MinimalCounterexampleContext P Target}
    {input : CT2.Input capability ctx}
    (source : CT2.SeparatingContextResidual capability ctx input) :
    targetContext source = ctx.toBranchContext :=
  rfl

theorem ambient_preserved
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    {capability : CT2.Capability.{uAmbient, uBranch, uCT2Piece, uInterface,
      uAbstract, uContext, uCandidate} P Target}
    {ctx : Core.MinimalCounterexampleContext P Target}
    {input : CT2.Input capability ctx}
    (source : CT2.SeparatingContextResidual capability ctx input) :
    (targetContext source).G = ctx.G :=
  rfl

theorem baseline_preserved
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    {capability : CT2.Capability.{uAmbient, uBranch, uCT2Piece, uInterface,
      uAbstract, uContext, uCandidate} P Target}
    {ctx : Core.MinimalCounterexampleContext P Target}
    {input : CT2.Input capability ctx}
    (source : CT2.SeparatingContextResidual capability ctx input) :
    (targetContext source).baseline = ctx.baseline :=
  rfl

theorem state_preserved
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    {capability : CT2.Capability.{uAmbient, uBranch, uCT2Piece, uInterface,
      uAbstract, uContext, uCandidate} P Target}
    {ctx : Core.MinimalCounterexampleContext P Target}
    {input : CT2.Input capability ctx}
    (source : CT2.SeparatingContextResidual capability ctx input) :
    (targetContext source).state = ctx.state :=
  rfl

theorem trigger_piece
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    {capability : CT2.Capability.{uAmbient, uBranch, uCT2Piece, uInterface,
      uAbstract, uContext, uCandidate} P Target}
    {ctx : Core.MinimalCounterexampleContext P Target}
    {input : CT2.Input capability ctx}
    {S : CT3.Spec.{uAmbient, uBranch, uCT3Piece, uCT3Context,
      uCT3Candidate, uRow} P}
    (targetCapability : CT3.Capability S)
    (sourceDiscovery : PieceDiscovery
      (CT2.SeparatingContextResidual capability ctx input) S.Piece)
    (source : CT2.SeparatingContextResidual capability ctx input)
    (seed : (rule targetCapability sourceDiscovery).Seed source) :
    (buildTrigger targetCapability sourceDiscovery source seed).piece =
      sourceDiscovery.piece source seed :=
  rfl

theorem enabled_generates
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    {capability : CT2.Capability.{uAmbient, uBranch, uCT2Piece, uInterface,
      uAbstract, uContext, uCandidate} P Target}
    {ctx : Core.MinimalCounterexampleContext P Target}
    {input : CT2.Input capability ctx}
    {S : CT3.Spec.{uAmbient, uBranch, uCT3Piece, uCT3Context,
      uCT3Candidate, uRow} P}
    (targetCapability : CT3.Capability S)
    (sourceDiscovery : PieceDiscovery
      (CT2.SeparatingContextResidual capability ctx input) S.Piece)
    (source : CT2.SeparatingContextResidual capability ctx input)
    (seed : (rule targetCapability sourceDiscovery).Seed source)
    (enabled : sourceDiscovery.discover source = .enabled seed) :
    ((rule targetCapability sourceDiscovery).attempt source).generated? =
      some ((rule targetCapability sourceDiscovery).generate source seed) := by
  change (rule targetCapability sourceDiscovery).discover source =
    .enabled seed at enabled
  simp [Core.Routing.RouteRule.attempt, enabled,
    Core.Routing.Attempt.generated?]

theorem disabled_generates_none
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    {capability : CT2.Capability.{uAmbient, uBranch, uCT2Piece, uInterface,
      uAbstract, uContext, uCandidate} P Target}
    {ctx : Core.MinimalCounterexampleContext P Target}
    {input : CT2.Input capability ctx}
    {S : CT3.Spec.{uAmbient, uBranch, uCT3Piece, uCT3Context,
      uCT3Candidate, uRow} P}
    (targetCapability : CT3.Capability S)
    (sourceDiscovery : PieceDiscovery
      (CT2.SeparatingContextResidual capability ctx input) S.Piece)
    (source : CT2.SeparatingContextResidual capability ctx input)
    (reject : (rule targetCapability sourceDiscovery).Seed source → False)
    (disabled : sourceDiscovery.discover source = .disabled reject) :
    ((rule targetCapability sourceDiscovery).attempt source).generated? = none := by
  change (rule targetCapability sourceDiscovery).discover source =
    .disabled reject at disabled
  simp [Core.Routing.RouteRule.attempt, disabled,
    Core.Routing.Attempt.generated?]

theorem generated_route_id
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    {capability : CT2.Capability.{uAmbient, uBranch, uCT2Piece, uInterface,
      uAbstract, uContext, uCandidate} P Target}
    {ctx : Core.MinimalCounterexampleContext P Target}
    {input : CT2.Input capability ctx}
    {S : CT3.Spec.{uAmbient, uBranch, uCT3Piece, uCT3Context,
      uCT3Candidate, uRow} P}
    (targetCapability : CT3.Capability S)
    (sourceDiscovery : PieceDiscovery
      (CT2.SeparatingContextResidual capability ctx input) S.Piece)
    (source : CT2.SeparatingContextResidual capability ctx input)
    (seed : (rule targetCapability sourceDiscovery).Seed source) :
    ((rule targetCapability sourceDiscovery).generate source seed).routeId =
      "CT2.residual.separatingContext->CT3" :=
  rfl

/-- Machine-readable route inventory.  The adapter value is problem-specific;
the adapter interface and every named construction or theorem are
framework-owned. -/
def routeContract : Core.RouteContract where
  routeId := "CT2.residual.separatingContext->CT3"
  sourceResidualKind := "CT2.residual.separatingContext"
  targetTacticId := "CT3"
  discovery := "StructuralExhaustion.Routes.CT2ToCT3.PieceDiscovery.discover"
  triggerConstructor := "StructuralExhaustion.Routes.CT2ToCT3.buildTrigger"
  soundnessTheorem := "StructuralExhaustion.Routes.CT2ToCT3.enabled_generates"
  contextPreservationTheorem :=
    "StructuralExhaustion.Routes.CT2ToCT3.branchContext_preserved"
  provenanceTheorem :=
    "StructuralExhaustion.Routes.CT2ToCT3.generated_route_id"
  selectionClass := .forced
  semanticDiscovery := .problemSemanticAdapter
    "StructuralExhaustion.Routes.CT2ToCT3.PieceDiscovery"
  problemSpecificInputs := [.targetCapability, .semanticDiscoveryAdapter]

end StructuralExhaustion.Routes.CT2ToCT3
