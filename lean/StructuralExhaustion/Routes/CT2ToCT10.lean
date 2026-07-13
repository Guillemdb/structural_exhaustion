import StructuralExhaustion.CT2.State
import StructuralExhaustion.CT10.Capability

namespace StructuralExhaustion.Routes.CT2ToCT10

universe uResidual uDatum uSeed
universe uAmbient uBranch uCT2Piece uInterface uAbstract uContext uCandidate
universe uClass uPromotion

/-!
Canonical typed routing from CT2 criticality residuals to CT10.  CT2 remains
consumer-blind; this module discovers CT10's finite datum collection and
constructs its route trigger at the inherited branch context.
-/

/-- Problem-specific finite-data discovery.  The seed is intentionally
abstract and may be uninhabited for a particular residual. -/
structure DataDiscovery (Residual : Type uResidual) (Datum : Type uDatum) where
  Seed : Residual → Type uSeed
  discover : (source : Residual) → Core.Routing.Discovery (Seed source)
  data : (source : Residual) → Seed source → Core.OrderedCollection Datum

def targetContext
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    {capability : CT2.Capability.{uAmbient, uBranch, uCT2Piece, uInterface,
      uAbstract, uContext, uCandidate} P Target}
    {ctx : Core.MinimalCounterexampleContext P Target}
    {input : CT2.Input capability ctx}
    (_source : CT2.CriticalityResidual capability ctx input) :
    Core.BranchContext P :=
  ctx.toBranchContext

def rule
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    {capability : CT2.Capability.{uAmbient, uBranch, uCT2Piece, uInterface,
      uAbstract, uContext, uCandidate} P Target}
    {ctx : Core.MinimalCounterexampleContext P Target}
    {input : CT2.Input capability ctx}
    (targetCapability : CT10.Capability.{uAmbient, uBranch, uDatum, uClass,
      uPromotion} P)
    (sourceDiscovery : DataDiscovery
      (CT2.CriticalityResidual capability ctx input) targetCapability.Datum) :
    Core.Routing.RouteRule
      (CT2.CriticalityResidual capability ctx input)
      (CT10.tacticInterface targetCapability) where
  routeId := "CT2.residual.criticality->CT10"
  targetContext := targetContext
  Seed := sourceDiscovery.Seed
  discover := sourceDiscovery.discover
  buildTrigger := fun source seed => ⟨sourceDiscovery.data source seed⟩

def buildTrigger
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    {capability : CT2.Capability.{uAmbient, uBranch, uCT2Piece, uInterface,
      uAbstract, uContext, uCandidate} P Target}
    {ctx : Core.MinimalCounterexampleContext P Target}
    {input : CT2.Input capability ctx}
    (targetCapability : CT10.Capability.{uAmbient, uBranch, uDatum, uClass,
      uPromotion} P)
    (sourceDiscovery : DataDiscovery
      (CT2.CriticalityResidual capability ctx input) targetCapability.Datum)
    (source : CT2.CriticalityResidual capability ctx input)
    (seed : (rule targetCapability sourceDiscovery).Seed source) :
    CT10.Trigger targetCapability (targetContext source) :=
  (rule targetCapability sourceDiscovery).buildTrigger source seed

/-- Construct the ordinary CT10 runner input after route generation. -/
def buildInput
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    {capability : CT2.Capability.{uAmbient, uBranch, uCT2Piece, uInterface,
      uAbstract, uContext, uCandidate} P Target}
    {ctx : Core.MinimalCounterexampleContext P Target}
    {input : CT2.Input capability ctx}
    (targetCapability : CT10.Capability.{uAmbient, uBranch, uDatum, uClass,
      uPromotion} P)
    (sourceDiscovery : DataDiscovery
      (CT2.CriticalityResidual capability ctx input) targetCapability.Datum)
    (source : CT2.CriticalityResidual capability ctx input)
    (seed : (rule targetCapability sourceDiscovery).Seed source) :
    CT10.Input targetCapability :=
  CT10.Input.ofTrigger (targetContext source)
    (buildTrigger targetCapability sourceDiscovery source seed)

theorem branchContext_preserved
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    {capability : CT2.Capability.{uAmbient, uBranch, uCT2Piece, uInterface,
      uAbstract, uContext, uCandidate} P Target}
    {ctx : Core.MinimalCounterexampleContext P Target}
    {input : CT2.Input capability ctx}
    (source : CT2.CriticalityResidual capability ctx input) :
    targetContext source = ctx.toBranchContext :=
  rfl

theorem ambient_preserved
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    {capability : CT2.Capability.{uAmbient, uBranch, uCT2Piece, uInterface,
      uAbstract, uContext, uCandidate} P Target}
    {ctx : Core.MinimalCounterexampleContext P Target}
    {input : CT2.Input capability ctx}
    (source : CT2.CriticalityResidual capability ctx input) :
    (targetContext source).G = ctx.G :=
  rfl

theorem baseline_preserved
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    {capability : CT2.Capability.{uAmbient, uBranch, uCT2Piece, uInterface,
      uAbstract, uContext, uCandidate} P Target}
    {ctx : Core.MinimalCounterexampleContext P Target}
    {input : CT2.Input capability ctx}
    (source : CT2.CriticalityResidual capability ctx input) :
    (targetContext source).baseline = ctx.baseline :=
  rfl

theorem state_preserved
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    {capability : CT2.Capability.{uAmbient, uBranch, uCT2Piece, uInterface,
      uAbstract, uContext, uCandidate} P Target}
    {ctx : Core.MinimalCounterexampleContext P Target}
    {input : CT2.Input capability ctx}
    (source : CT2.CriticalityResidual capability ctx input) :
    (targetContext source).state = ctx.state :=
  rfl

theorem input_context_preserved
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    {capability : CT2.Capability.{uAmbient, uBranch, uCT2Piece, uInterface,
      uAbstract, uContext, uCandidate} P Target}
    {ctx : Core.MinimalCounterexampleContext P Target}
    {input : CT2.Input capability ctx}
    (targetCapability : CT10.Capability.{uAmbient, uBranch, uDatum, uClass,
      uPromotion} P)
    (sourceDiscovery : DataDiscovery
      (CT2.CriticalityResidual capability ctx input) targetCapability.Datum)
    (source : CT2.CriticalityResidual capability ctx input)
    (seed : (rule targetCapability sourceDiscovery).Seed source) :
    (buildInput targetCapability sourceDiscovery source seed).context =
      ctx.toBranchContext :=
  rfl

theorem input_data_preserved
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    {capability : CT2.Capability.{uAmbient, uBranch, uCT2Piece, uInterface,
      uAbstract, uContext, uCandidate} P Target}
    {ctx : Core.MinimalCounterexampleContext P Target}
    {input : CT2.Input capability ctx}
    (targetCapability : CT10.Capability.{uAmbient, uBranch, uDatum, uClass,
      uPromotion} P)
    (sourceDiscovery : DataDiscovery
      (CT2.CriticalityResidual capability ctx input) targetCapability.Datum)
    (source : CT2.CriticalityResidual capability ctx input)
    (seed : (rule targetCapability sourceDiscovery).Seed source) :
    (buildInput targetCapability sourceDiscovery source seed).data =
      sourceDiscovery.data source seed :=
  rfl

theorem enabled_generates
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    {capability : CT2.Capability.{uAmbient, uBranch, uCT2Piece, uInterface,
      uAbstract, uContext, uCandidate} P Target}
    {ctx : Core.MinimalCounterexampleContext P Target}
    {input : CT2.Input capability ctx}
    (targetCapability : CT10.Capability.{uAmbient, uBranch, uDatum, uClass,
      uPromotion} P)
    (sourceDiscovery : DataDiscovery
      (CT2.CriticalityResidual capability ctx input) targetCapability.Datum)
    (source : CT2.CriticalityResidual capability ctx input)
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
    (targetCapability : CT10.Capability.{uAmbient, uBranch, uDatum, uClass,
      uPromotion} P)
    (sourceDiscovery : DataDiscovery
      (CT2.CriticalityResidual capability ctx input) targetCapability.Datum)
    (source : CT2.CriticalityResidual capability ctx input)
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
    (targetCapability : CT10.Capability.{uAmbient, uBranch, uDatum, uClass,
      uPromotion} P)
    (sourceDiscovery : DataDiscovery
      (CT2.CriticalityResidual capability ctx input) targetCapability.Datum)
    (source : CT2.CriticalityResidual capability ctx input)
    (seed : (rule targetCapability sourceDiscovery).Seed source) :
    ((rule targetCapability sourceDiscovery).generate source seed).routeId =
      "CT2.residual.criticality->CT10" :=
  rfl

def routeContract : Core.RouteContract where
  routeId := "CT2.residual.criticality->CT10"
  sourceResidualKind := "CT2.residual.criticality"
  targetTacticId := "CT10"
  discovery := "StructuralExhaustion.Routes.CT2ToCT10.DataDiscovery.discover"
  triggerConstructor := "StructuralExhaustion.Routes.CT2ToCT10.buildTrigger"
  soundnessTheorem := "StructuralExhaustion.Routes.CT2ToCT10.enabled_generates"
  contextPreservationTheorem :=
    "StructuralExhaustion.Routes.CT2ToCT10.branchContext_preserved"
  provenanceTheorem :=
    "StructuralExhaustion.Routes.CT2ToCT10.generated_route_id"
  selectionClass := .forced
  semanticDiscovery := .problemSemanticAdapter
    "StructuralExhaustion.Routes.CT2ToCT10.DataDiscovery"
  problemSpecificInputs := [.targetCapability, .semanticDiscoveryAdapter]

end StructuralExhaustion.Routes.CT2ToCT10
