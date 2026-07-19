import StructuralExhaustion.CT2.State
import StructuralExhaustion.CT3.Execution

namespace StructuralExhaustion.Routes.CT2ToCT3

universe uResidual uPiece uSeed uLedger
universe uAmbient uBranch uCT2Piece uInterface uAbstract uContext uCandidate
universe uCT3Piece uCT3Context uCT3Candidate uRow

/-- Stable identity of this transition profile. -/
def transitionId : String := "CT2.residual.separatingContext->CT3"

/-!
Canonical typed routing from CT2 separating-context residuals to CT3.

CT2 never imports CT3.  The transition profile owns the only cross-tactic dependency,
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

/-- CT2's inherited branch is the CT3 transition index. -/
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

/-- Canonical executable CT2→CT3 transition.  Piece discovery is the sole
problem-semantic input; exact stage transport and CT3 execution are owned by
the transition kernel. -/
def transition
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
    Core.Routing.CTTransition .ct2 .ct3
      (CT2.SeparatingContextResidual capability ctx input)
      targetCapability.executableInterface :=
  Core.Routing.CTTransition.ofAdapter transitionId targetContext
    sourceDiscovery.Seed sourceDiscovery.discover
    (fun source seed => ⟨sourceDiscovery.piece source seed⟩)

/-- Discover and execute CT3 from an exact CT2 separating residual.  The
enabled branch chains onward only through its accumulated `ledgerStage`. -/
def advance
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
    {Ledger : Sort uLedger}
    (current : Ledger → CT2.SeparatingContextResidual capability ctx input)
    (source : Core.Routing.ResidualStage .ct2 Ledger) :
    ((transition targetCapability sourceDiscovery).onLedger current).Outcome source :=
  Core.Routing.CTTransition.runOnLedger
    (transition targetCapability sourceDiscovery) current source

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

/-! The public proof surface is stated only in terms of executable stages.
No application constructs a detached seed, trigger, or transport record. -/

/-- An enabled stage contains exactly the discovered CT3 piece and the
reference execution on that piece. -/
theorem enabled_sound
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
    {Ledger : Sort uLedger}
    (current : Ledger → CT2.SeparatingContextResidual capability ctx input)
    (source : Core.Routing.ResidualStage .ct2 Ledger)
    (stage : ((transition targetCapability sourceDiscovery).onLedger current).EnabledStage
      source)
    (ran : advance targetCapability sourceDiscovery current source = .enabled stage) :
    sourceDiscovery.discover (current source.output) =
      .enabled stage.execution.seed ∧
      (((transition targetCapability sourceDiscovery).onLedger current).trigger source
        stage.execution.seed).piece =
          sourceDiscovery.piece (current source.output) stage.execution.seed ∧
      stage.targetResult = targetCapability.executableInterface.execute
        (((transition targetCapability sourceDiscovery).onLedger current).targetContext
          source)
        (((transition targetCapability sourceDiscovery).onLedger current).trigger source
          stage.execution.seed) :=
  by
    unfold advance Core.Routing.CTTransition.runOnLedger at ran
    unfold Core.Routing.CTTransition.run at ran
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
    {S : CT3.Spec.{uAmbient, uBranch, uCT3Piece, uCT3Context,
      uCT3Candidate, uRow} P}
    (targetCapability : CT3.Capability S)
    (sourceDiscovery : PieceDiscovery
      (CT2.SeparatingContextResidual capability ctx input) S.Piece)
    {Ledger : Sort uLedger}
    (current : Ledger → CT2.SeparatingContextResidual capability ctx input)
    (source : Core.Routing.ResidualStage .ct2 Ledger)
    (notEnabled : ∀ stage :
      ((transition targetCapability sourceDiscovery).onLedger current).EnabledStage
        source,
      advance targetCapability sourceDiscovery current source ≠ .enabled stage) :
    IsEmpty (sourceDiscovery.Seed (current source.output)) := by
  constructor
  intro seed
  cases outcomeEq : advance targetCapability sourceDiscovery current source with
  | enabled stage => exact (notEnabled stage outcomeEq).elim
  | disabled reject _discovered => exact reject seed

@[simp] theorem source_tactic_id
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
    (transition targetCapability sourceDiscovery).sourceTacticId = "CT2" := rfl

@[simp] theorem target_tactic_id
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
    (transition targetCapability sourceDiscovery).targetTacticId = "CT3" := rfl

@[simp] theorem transition_profile_id
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
    (transition targetCapability sourceDiscovery).profileId = transitionId := rfl

/-- Machine-readable executable profile for the CT2→CT3 family. -/
def transitionContract : Core.CTTransitionProfileContract where
  profileId := transitionId
  sourceTacticId := "CT2"
  targetTacticId := "CT3"
  sourceResidualKind := "CT2.residual.separatingContext"
  targetExecutableInterface :=
    "StructuralExhaustion.CT3.Capability.executableInterface"
  transitionConstructor :=
    "StructuralExhaustion.Routes.CT2ToCT3.transition"
  advanceExecutor := "StructuralExhaustion.Routes.CT2ToCT3.advance"
  selectionClass := .forced
  semanticDiscovery := .problemSemanticAdapter
    "StructuralExhaustion.Routes.CT2ToCT3.PieceDiscovery"
  problemSpecificInputs := [.targetCapability, .semanticDiscoveryAdapter]

end StructuralExhaustion.Routes.CT2ToCT3
