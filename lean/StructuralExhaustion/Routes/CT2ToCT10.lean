import StructuralExhaustion.CT2.State
import StructuralExhaustion.CT10.Automation

namespace StructuralExhaustion.Routes.CT2ToCT10

universe uResidual uDatum uSeed uLedger
universe uAmbient uBranch uCT2Piece uInterface uAbstract uContext uCandidate
universe uClass uPromotion

/-- Stable identity of this transition profile. -/
def transitionId : String := "CT2.residual.criticality->CT10"

/-!
Canonical typed routing from CT2 criticality residuals to CT10.  CT2 remains
consumer-blind; this module discovers CT10's finite datum collection and
constructs its transition trigger at the inherited branch context.
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

/-- Canonical executable CT2→CT10 transition.  Data discovery remains the
problem-specific semantic adapter; target execution and predecessor
preservation are framework-owned. -/
def transition
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
    Core.Routing.CTTransition .ct2 .ct10
      (CT2.CriticalityResidual capability ctx input)
      targetCapability.executableInterface :=
  Core.Routing.CTTransition.ofAdapter transitionId targetContext
    sourceDiscovery.Seed sourceDiscovery.discover
    (fun source seed => ⟨sourceDiscovery.data source seed⟩)

/-- Discover and execute CT10 from an exact CT2 criticality residual.  The
enabled branch chains onward only through its accumulated `ledgerStage`. -/
def advance
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
    {Ledger : Sort uLedger}
    (current : Ledger → CT2.CriticalityResidual capability ctx input)
    (source : Core.Routing.ResidualStage .ct2 Ledger) :
    Core.Routing.CTTransition.LedgerOutcome
      ((transition targetCapability sourceDiscovery).onLedger current) source :=
  Core.Routing.CTTransition.runLedgerOnLedger
    (transition targetCapability sourceDiscovery) current source

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

/-! The public proof surface is stated only over executable stages. -/

/-- Enabled execution retains the discovered collection in the exact CT10
trigger and executes the canonical CT10 entry at the inherited context. -/
theorem enabled_sound
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
    {Ledger : Sort uLedger}
    (current : Ledger → CT2.CriticalityResidual capability ctx input)
    (source : Core.Routing.ResidualStage .ct2 Ledger)
    (stage : Core.Routing.ResidualStage .ct10
      (((transition targetCapability sourceDiscovery).onLedger current).EnabledStage source))
    (ran : advance targetCapability sourceDiscovery current source = .enabled stage) :
    sourceDiscovery.discover (current source.output) =
      .enabled stage.output.execution.seed ∧
      (((transition targetCapability sourceDiscovery).onLedger current).trigger source
        stage.output.execution.seed).data =
          sourceDiscovery.data (current source.output) stage.output.execution.seed ∧
      stage.output.targetResult = targetCapability.executableInterface.execute
        (((transition targetCapability sourceDiscovery).onLedger current).targetContext
          source)
        (((transition targetCapability sourceDiscovery).onLedger current).trigger source
          stage.output.execution.seed) := by
  unfold advance Core.Routing.CTTransition.runLedgerOnLedger at ran
  unfold Core.Routing.CTTransition.runLedger at ran
  split at ran
  · cases ran
    exact ⟨by assumption, rfl, rfl⟩
  · contradiction

/-- If automatic execution has no enabled stage, discovery has no seed. -/
theorem disabled_sound
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
    {Ledger : Sort uLedger}
    (current : Ledger → CT2.CriticalityResidual capability ctx input)
    (source : Core.Routing.ResidualStage .ct2 Ledger)
    (notEnabled : ∀ stage : Core.Routing.ResidualStage .ct10
      (((transition targetCapability sourceDiscovery).onLedger current).EnabledStage source),
      advance targetCapability sourceDiscovery current source ≠ .enabled stage) :
    IsEmpty (sourceDiscovery.Seed (current source.output)) := by
  constructor
  intro seed
  cases outcomeEq : advance targetCapability sourceDiscovery current source with
  | enabled stage => exact (notEnabled stage outcomeEq).elim
  | disabled rejected => exact rejected.output.reject seed

@[simp] theorem source_tactic_id
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
    (transition targetCapability sourceDiscovery).sourceTacticId = "CT2" := rfl

@[simp] theorem target_tactic_id
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
    (transition targetCapability sourceDiscovery).targetTacticId = "CT10" := rfl

@[simp] theorem transition_profile_id
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
    (transition targetCapability sourceDiscovery).profileId = transitionId := rfl

def transitionContract : Core.CTTransitionProfileContract where
  profileId := transitionId
  sourceTacticId := "CT2"
  targetTacticId := "CT10"
  sourceResidualKind := "CT2.residual.criticality"
  targetExecutableInterface :=
    "StructuralExhaustion.CT10.Capability.executableInterface"
  transitionConstructor :=
    "StructuralExhaustion.Routes.CT2ToCT10.transition"
  advanceExecutor := "StructuralExhaustion.Routes.CT2ToCT10.advance"
  selectionClass := .forced
  semanticDiscovery := .problemSemanticAdapter
    "StructuralExhaustion.Routes.CT2ToCT10.DataDiscovery"
  problemSpecificInputs := [.targetCapability, .semanticDiscoveryAdapter]

end StructuralExhaustion.Routes.CT2ToCT10
