import StructuralExhaustion.CT1.Automation
import StructuralExhaustion.CT2.Automation
import StructuralExhaustion.CT2.LocalDeletion

namespace StructuralExhaustion.Routes.CT1ToCT2

universe uAmbient uBranch uIndex uWitness uLedger
universe uPiece uInterface uAbstract uContext uCandidate

/-- Stable identity of the full CT1→CT2 replacement profile. -/
def transitionId : String := "CT1.residual.avoiding->CT2"

/-- Existentially package the predecessor equivalence index of CT1's sole
semantic residual.  The inherited branch remains a dependent index. -/
structure PackedAvoiding
    {P : Core.Problem.{uAmbient, uBranch}}
    (S : CT1.Spec.{uIndex, uWitness} P) (input : CT1.Input P) : Type where
  equivalence : CT1.EquivalenceState S input
  state : CT1.AvoidingState S input equivalence

namespace PackedAvoiding

/-- Extract CT1's semantic residual from a result already known to have
reached the avoiding terminal. -/
def ofResult
    {P : Core.Problem.{uAmbient, uBranch}}
    {S : CT1.Spec.{uIndex, uWitness} P} {input : CT1.Input P}
    (result : CT1.ExecutionResult S input)
    (terminal : result.terminal = .avoiding) : PackedAvoiding S input := by
  cases result with
  | mk terminalId path outcome =>
      cases outcome with
      | c1 certificate => cases terminal
      | avoiding state => exact ⟨_, state⟩

end PackedAvoiding

/-- Extend the CT1 residual by the one shared minimality theorem.  The branch
context itself is inherited definitionally through `toAvoidingContext`. -/
def targetContext
    {P : Core.Problem.{uAmbient, uBranch}}
    {S : CT1.Spec.{uIndex, uWitness} P} {input : CT1.Input P}
    (minimality : Core.MinimalityKernel P (CT1.Target S) input.context)
    (source : PackedAvoiding S input) :
    Core.MinimalCounterexampleContext P (CT1.Target S) :=
  Core.MinimalCounterexampleContext.ofAvoiding
    source.state.toAvoidingContext minimality

/-- Canonical executable CT1→CT2 transition for the full replacement
profile.  Discovery, trigger construction, execution, and predecessor
retention are all owned by the transition kernel. -/
def transition
    {P : Core.Problem.{uAmbient, uBranch}}
    {S : CT1.Spec.{uIndex, uWitness} P} {input : CT1.Input P}
    (capability : CT2.Capability.{uAmbient, uBranch, uPiece, uInterface,
      uAbstract, uContext, uCandidate} P (CT1.Target S))
    (minimality : Core.MinimalityKernel P (CT1.Target S) input.context) :
    Core.Routing.CTTransition .ct1 .ct2 (PackedAvoiding S input)
      capability.executableInterface :=
  Core.Routing.CTTransition.ofAdapter transitionId (targetContext minimality)
    (fun source => CT2.Input capability (targetContext minimality source))
    (fun source => capability.discover (targetContext minimality source))
    (fun _source trigger => trigger)

/-- Discover and execute the full CT2 profile from an exact CT1 residual.
The enabled outcome is the complete `EnabledStage`; every later edge chains
from its framework-owned `ledgerStage`, not from the bare result projection. -/
def advance
    {P : Core.Problem.{uAmbient, uBranch}}
    {S : CT1.Spec.{uIndex, uWitness} P} {input : CT1.Input P}
    (capability : CT2.Capability.{uAmbient, uBranch, uPiece, uInterface,
      uAbstract, uContext, uCandidate} P (CT1.Target S))
    (minimality : Core.MinimalityKernel P (CT1.Target S) input.context)
    {Ledger : Sort uLedger} (current : Ledger → PackedAvoiding S input)
    (source : Core.Routing.ResidualStage .ct1 Ledger) :
    ((transition capability minimality).onLedger current).Outcome source :=
  Core.Routing.CTTransition.runOnLedger
    (transition capability minimality) current source

/-- The complete inherited branch context is preserved definitionally. -/
theorem branchContext_preserved
    {P : Core.Problem.{uAmbient, uBranch}}
    {S : CT1.Spec.{uIndex, uWitness} P} {input : CT1.Input P}
    (minimality : Core.MinimalityKernel P (CT1.Target S) input.context)
    (source : PackedAvoiding S input) :
    (targetContext minimality source).toBranchContext = input.context :=
  rfl

theorem ambient_preserved
    {P : Core.Problem.{uAmbient, uBranch}}
    {S : CT1.Spec.{uIndex, uWitness} P} {input : CT1.Input P}
    (minimality : Core.MinimalityKernel P (CT1.Target S) input.context)
    (source : PackedAvoiding S input) :
    (targetContext minimality source).G = input.context.G :=
  rfl

theorem state_preserved
    {P : Core.Problem.{uAmbient, uBranch}}
    {S : CT1.Spec.{uIndex, uWitness} P} {input : CT1.Input P}
    (minimality : Core.MinimalityKernel P (CT1.Target S) input.context)
    (source : PackedAvoiding S input) :
    (targetContext minimality source).state = input.context.state :=
  rfl

theorem baseline_preserved
    {P : Core.Problem.{uAmbient, uBranch}}
    {S : CT1.Spec.{uIndex, uWitness} P} {input : CT1.Input P}
    (minimality : Core.MinimalityKernel P (CT1.Target S) input.context)
    (source : PackedAvoiding S input) :
    (targetContext minimality source).baseline = input.context.baseline :=
  rfl

theorem avoidance_preserved
    {P : Core.Problem.{uAmbient, uBranch}}
    {S : CT1.Spec.{uIndex, uWitness} P} {input : CT1.Input P}
    (minimality : Core.MinimalityKernel P (CT1.Target S) input.context)
    (source : PackedAvoiding S input) :
    (targetContext minimality source).avoids = source.state.targetAvoiding :=
  rfl

/-- Every enabled transition contains the exact proper/admissible CT2 input
selected by generic capability discovery. -/
theorem enabled_sound
    {P : Core.Problem.{uAmbient, uBranch}}
    {S : CT1.Spec.{uIndex, uWitness} P} {input : CT1.Input P}
    (capability : CT2.Capability.{uAmbient, uBranch, uPiece, uInterface,
      uAbstract, uContext, uCandidate} P (CT1.Target S))
    (minimality : Core.MinimalityKernel P (CT1.Target S) input.context)
    {Ledger : Sort uLedger} (current : Ledger → PackedAvoiding S input)
    (source : Core.Routing.ResidualStage .ct1 Ledger)
    (stage : ((transition capability minimality).onLedger current).EnabledStage
      source) :
    capability.pieces.Proper stage.execution.seed.seed.piece ∧
      capability.pieces.Admissible
        (targetContext minimality (current source.output)).state
          stage.execution.seed.seed.piece :=
  ⟨stage.execution.seed.seed.proper, stage.execution.seed.seed.admissible⟩

/-- Disabled discovery is an exact mathematical absence result, not a scope
tag: every enumerated piece fails properness or admissibility. -/
theorem disabled_sound
    {P : Core.Problem.{uAmbient, uBranch}}
    {S : CT1.Spec.{uIndex, uWitness} P} {input : CT1.Input P}
    (capability : CT2.Capability.{uAmbient, uBranch, uPiece, uInterface,
      uAbstract, uContext, uCandidate} P (CT1.Target S))
    (minimality : Core.MinimalityKernel P (CT1.Target S) input.context)
    {Ledger : Sort uLedger} (current : Ledger → PackedAvoiding S input)
    (source : Core.Routing.ResidualStage .ct1 Ledger)
    (notEnabled : ∀ stage :
      ((transition capability minimality).onLedger current).EnabledStage source,
      advance capability minimality current source ≠ .enabled stage) :
    ∀ piece : capability.pieces.Piece
      (targetContext minimality (current source.output)).G,
      ¬ capability.pieces.Proper piece ∨
        ¬ capability.pieces.Admissible
          (targetContext minimality (current source.output)).state piece := by
  intro piece
  cases properDecision : capability.pieces.properDecidable piece with
  | isFalse notProper => exact Or.inl notProper
  | isTrue proper =>
      cases admissibleDecision : capability.pieces.admissibleDecidable
          (targetContext minimality (current source.output)).state piece with
      | isFalse notAdmissible => exact Or.inr notAdmissible
      | isTrue admissible =>
          cases outcomeEq : advance capability minimality current source with
          | enabled stage => exact (notEnabled stage outcomeEq).elim
          | disabled reject _discovered =>
              exact (reject ⟨⟨piece, proper, admissible⟩⟩).elim

@[simp] theorem transition_profile_id
    {P : Core.Problem.{uAmbient, uBranch}}
    {S : CT1.Spec.{uIndex, uWitness} P} {input : CT1.Input P}
    (capability : CT2.Capability.{uAmbient, uBranch, uPiece, uInterface,
      uAbstract, uContext, uCandidate} P (CT1.Target S))
    (minimality : Core.MinimalityKernel P (CT1.Target S) input.context) :
    (transition capability minimality).profileId = transitionId := rfl

/-- Executable full-profile contract for the CT1→CT2 family. -/
def transitionContract : Core.CTTransitionProfileContract where
  profileId := transitionId
  sourceTacticId := "CT1"
  targetTacticId := "CT2"
  sourceResidualKind := "CT1.residual.avoiding"
  targetExecutableInterface :=
    "StructuralExhaustion.CT2.Capability.executableInterface"
  transitionConstructor :=
    "StructuralExhaustion.Routes.CT1ToCT2.transition"
  advanceExecutor := "StructuralExhaustion.Routes.CT1ToCT2.advance"
  selectionClass := .priority
  semanticDiscovery := .capabilityDiscovery
  problemSpecificInputs := [.targetCapability, .minimalityKernel]

end StructuralExhaustion.Routes.CT1ToCT2

namespace StructuralExhaustion.Routes.CT1ToCT2.LocalDeletion

universe uAmbient uBranch uIndex uWitness uPiece uCode uLedger

open StructuralExhaustion.Routes.CT1ToCT2

/-- Stable identity of the local-deletion CT1→CT2 profile. -/
def transitionId : String := "CT1.residual.avoiding->CT2.localDeletion"

/-!
# CT1 avoidance to local-deletion CT2

This transition is the target-decision-free profile of CT1-to-CT2.  It preserves
the CT1 branch through the shared minimality kernel and searches only the
consumer's declared local piece enumeration.
-/

/-- Canonical CT1→CT2 local-deletion profile.  It inhabits the same typed
CT pair as the full replacement profile while retaining its smaller trigger
and result types through the closure rule's executable interface. -/
def transition
    {P : Core.Problem.{uAmbient, uBranch}}
    {S : CT1.Spec.{uIndex, uWitness} P} {input : CT1.Input P}
    (capability : CT2.LocalDeletionCapability.{uAmbient, uBranch, uPiece} P)
    (minimality : Core.MinimalityKernel P (CT1.Target S) input.context)
    (closure : CT2.LocalDeletionClosureRule (Target := CT1.Target S)
      capability) :
    Core.Routing.CTTransition .ct1 .ct2 (PackedAvoiding S input)
      closure.executableInterface :=
  Core.Routing.CTTransition.ofAdapter transitionId
    (CT1ToCT2.targetContext minimality)
    (fun source => CT2.LocalDeletionInput capability
      (CT1ToCT2.targetContext minimality source))
    (fun source => capability.discover
      (CT1ToCT2.targetContext minimality source))
    (fun _source trigger => trigger)

/-- Discover and execute local deletion from an exact CT1 residual.  An
enabled caller continues through the returned stage's `ledgerStage`, thereby
retaining the CT1 predecessor as well as the CT2 execution. -/
def advance
    {P : Core.Problem.{uAmbient, uBranch}}
    {S : CT1.Spec.{uIndex, uWitness} P} {input : CT1.Input P}
    (capability : CT2.LocalDeletionCapability.{uAmbient, uBranch, uPiece} P)
    (minimality : Core.MinimalityKernel P (CT1.Target S) input.context)
    (closure : CT2.LocalDeletionClosureRule (Target := CT1.Target S)
      capability)
    {Ledger : Sort uLedger} (current : Ledger → PackedAvoiding S input)
    (source : Core.Routing.ResidualStage .ct1 Ledger) :
    ((transition capability minimality closure).onLedger current).Outcome source :=
  Core.Routing.CTTransition.runOnLedger
    (transition capability minimality closure) current source

/-- The complete inherited branch context is definitionally preserved. -/
theorem branchContext_preserved
    {P : Core.Problem.{uAmbient, uBranch}}
    {S : CT1.Spec.{uIndex, uWitness} P} {input : CT1.Input P}
    (minimality : Core.MinimalityKernel P (CT1.Target S) input.context)
    (source : PackedAvoiding S input) :
    (CT1ToCT2.targetContext minimality source).toBranchContext =
      input.context :=
  CT1ToCT2.branchContext_preserved minimality source

theorem ambient_preserved
    {P : Core.Problem.{uAmbient, uBranch}}
    {S : CT1.Spec.{uIndex, uWitness} P} {input : CT1.Input P}
    (minimality : Core.MinimalityKernel P (CT1.Target S) input.context)
    (source : PackedAvoiding S input) :
    (CT1ToCT2.targetContext minimality source).G = input.context.G :=
  CT1ToCT2.ambient_preserved minimality source

theorem state_preserved
    {P : Core.Problem.{uAmbient, uBranch}}
    {S : CT1.Spec.{uIndex, uWitness} P} {input : CT1.Input P}
    (minimality : Core.MinimalityKernel P (CT1.Target S) input.context)
    (source : PackedAvoiding S input) :
    (CT1ToCT2.targetContext minimality source).state = input.context.state :=
  CT1ToCT2.state_preserved minimality source

theorem baseline_preserved
    {P : Core.Problem.{uAmbient, uBranch}}
    {S : CT1.Spec.{uIndex, uWitness} P} {input : CT1.Input P}
    (minimality : Core.MinimalityKernel P (CT1.Target S) input.context)
    (source : PackedAvoiding S input) :
    (CT1ToCT2.targetContext minimality source).baseline =
      input.context.baseline :=
  CT1ToCT2.baseline_preserved minimality source

theorem avoidance_preserved
    {P : Core.Problem.{uAmbient, uBranch}}
    {S : CT1.Spec.{uIndex, uWitness} P} {input : CT1.Input P}
    (minimality : Core.MinimalityKernel P (CT1.Target S) input.context)
    (source : PackedAvoiding S input) :
    (CT1ToCT2.targetContext minimality source).avoids =
      source.state.targetAvoiding :=
  CT1ToCT2.avoidance_preserved minimality source

/-- Enabled execution returns exactly one proper admissible local piece and
the canonical local-deletion run on that piece. -/
theorem enabled_sound
    {P : Core.Problem.{uAmbient, uBranch}}
    {S : CT1.Spec.{uIndex, uWitness} P} {input : CT1.Input P}
    (capability : CT2.LocalDeletionCapability.{uAmbient, uBranch, uPiece} P)
    (minimality : Core.MinimalityKernel P (CT1.Target S) input.context)
    (closure : CT2.LocalDeletionClosureRule (Target := CT1.Target S)
      capability)
    {Ledger : Sort uLedger} (current : Ledger → PackedAvoiding S input)
    (source : Core.Routing.ResidualStage .ct1 Ledger)
    (stage : ((transition capability minimality closure).onLedger current).EnabledStage
      source)
    (ran : advance capability minimality closure current source = .enabled stage) :
    capability.pieces.Proper stage.execution.seed.seed.piece ∧
      capability.pieces.Admissible
        (CT1ToCT2.targetContext minimality (current source.output)).state
          stage.execution.seed.seed.piece ∧
      stage.targetResult = closure.executableInterface.execute
        (((transition capability minimality closure).onLedger current).targetContext
          source)
        (((transition capability minimality closure).onLedger current).trigger source
          stage.execution.seed) := by
  have proper := stage.execution.seed.seed.proper
  have admissible := stage.execution.seed.seed.admissible
  unfold advance Core.Routing.CTTransition.runOnLedger at ran
  unfold Core.Routing.CTTransition.run at ran
  split at ran
  · cases ran
    exact ⟨proper, admissible, rfl⟩
  · contradiction

/-- Disabled discovery proves that every declared piece fails properness or
admissibility. -/
theorem disabled_sound
    {P : Core.Problem.{uAmbient, uBranch}}
    {S : CT1.Spec.{uIndex, uWitness} P} {input : CT1.Input P}
    (capability : CT2.LocalDeletionCapability.{uAmbient, uBranch, uPiece} P)
    (minimality : Core.MinimalityKernel P (CT1.Target S) input.context)
    (closure : CT2.LocalDeletionClosureRule (Target := CT1.Target S)
      capability)
    {Ledger : Sort uLedger} (current : Ledger → PackedAvoiding S input)
    (source : Core.Routing.ResidualStage .ct1 Ledger)
    (notEnabled : ∀ stage :
      ((transition capability minimality closure).onLedger current).EnabledStage source,
      advance capability minimality closure current source ≠ .enabled stage) :
    ∀ piece : capability.pieces.Piece
        (CT1ToCT2.targetContext minimality (current source.output)).G,
      ¬ capability.pieces.Proper piece ∨
        ¬ capability.pieces.Admissible
          (CT1ToCT2.targetContext minimality (current source.output)).state piece := by
  intro piece
  cases capability.pieces.properDecidable piece with
  | isFalse notProper => exact Or.inl notProper
  | isTrue proper =>
      cases capability.pieces.admissibleDecidable
          (CT1ToCT2.targetContext minimality (current source.output)).state piece with
      | isFalse notAdmissible => exact Or.inr notAdmissible
      | isTrue admissible =>
          cases outcomeEq : advance capability minimality closure current source with
          | enabled stage => exact (notEnabled stage outcomeEq).elim
          | disabled reject _discovered =>
              exact (reject ⟨⟨piece, proper, admissible⟩⟩).elim

/-- A valid local deletion closure forces transition discovery to be disabled:
an enabled trigger executes the deletion-C2 path and contradicts minimality. -/
theorem advance_not_enabled_of_closure
    {P : Core.Problem.{uAmbient, uBranch}}
    {S : CT1.Spec.{uIndex, uWitness} P} {input : CT1.Input P}
    {capability : CT2.LocalDeletionCapability.{uAmbient, uBranch, uPiece} P}
    (minimality : Core.MinimalityKernel P (CT1.Target S) input.context)
    {Ledger : Sort uLedger} (current : Ledger → PackedAvoiding S input)
    (source : Core.Routing.ResidualStage .ct1 Ledger)
    (closure : CT2.LocalDeletionClosureRule (Target := CT1.Target S)
      capability) :
    ∀ stage :
      ((transition capability minimality closure).onLedger current).EnabledStage source,
      advance capability minimality closure current source ≠ .enabled stage := by
  intro stage ran
  exact stage.targetResult.verified

@[simp] theorem transition_profile_id
    {P : Core.Problem.{uAmbient, uBranch}}
    {S : CT1.Spec.{uIndex, uWitness} P} {input : CT1.Input P}
    (capability : CT2.LocalDeletionCapability.{uAmbient, uBranch, uPiece} P)
    (minimality : Core.MinimalityKernel P (CT1.Target S) input.context)
    (closure : CT2.LocalDeletionClosureRule (Target := CT1.Target S)
      capability) :
    (transition capability minimality closure).profileId = transitionId := rfl

/-! ## Certificate-target composition profile -/

/-- Reusable data for routing the avoiding residual of any proof-carrying CT1
target encoding into a target-decision-free local CT2 deletion capability.
The public-target closure rule is transported through the CT1 bridge by the
framework. -/
structure CertificateProfile
    {P : Core.Problem.{uAmbient, uBranch}}
    (PublicTarget : P.Ambient → Prop) where
  encoding :
    CT1.TargetCertificateEncoding.{uAmbient, uBranch, uCode} PublicTarget
  capability : CT2.LocalDeletionCapability.{uAmbient, uBranch, uPiece} P
  closure : CT2.LocalDeletionClosureRule (Target := PublicTarget) capability

namespace CertificateProfile

/-- The CT1 input is the exact branch inherited from the public minimal
counterexample context. -/
def input
    {P : Core.Problem.{uAmbient, uBranch}}
    {PublicTarget : P.Ambient → Prop}
    (_profile : CertificateProfile.{uAmbient, uBranch, uPiece, uCode}
      PublicTarget)
    (ctx : Core.MinimalCounterexampleContext P PublicTarget) : CT1.Input P :=
  ⟨ctx.toBranchContext⟩

/-- Execute the proof-carrying CT1 avoiding branch selected by the public
minimal-counterexample context. -/
def runAvoiding
    {P : Core.Problem.{uAmbient, uBranch}}
    {PublicTarget : P.Ambient → Prop}
    (profile : CertificateProfile.{uAmbient, uBranch, uPiece, uCode}
      PublicTarget)
    (ctx : Core.MinimalCounterexampleContext P PublicTarget) :=
  profile.encoding.runAvoiding (profile.input ctx) ctx.avoids

/-- Extract the actual terminal-indexed avoiding residual from CT1. -/
def avoidingSource
    {P : Core.Problem.{uAmbient, uBranch}}
    {PublicTarget : P.Ambient → Prop}
    (profile : CertificateProfile.{uAmbient, uBranch, uPiece, uCode}
      PublicTarget)
    (ctx : Core.MinimalCounterexampleContext P PublicTarget) :
    PackedAvoiding profile.encoding.spec (profile.input ctx) :=
  PackedAvoiding.ofResult (profile.runAvoiding ctx).result
    (profile.runAvoiding ctx).terminal_eq

/-- Transport public-target minimality through the exact CT1 target bridge. -/
def targetMinimality
    {P : Core.Problem.{uAmbient, uBranch}}
    {PublicTarget : P.Ambient → Prop}
    (profile : CertificateProfile.{uAmbient, uBranch, uPiece, uCode}
      PublicTarget)
    (ctx : Core.MinimalCounterexampleContext P PublicTarget) :
    Core.MinimalityKernel P (CT1.Target profile.encoding.spec)
      (profile.input ctx).context := by
  intro object smaller baseline
  exact profile.encoding.bridge.target_of_publicTarget
    (ctx.minimal object smaller baseline)

/-- Transport the public local-deletion closure through the same CT1 bridge. -/
def routedClosure
    {P : Core.Problem.{uAmbient, uBranch}}
    {PublicTarget : P.Ambient → Prop}
    (profile : CertificateProfile.{uAmbient, uBranch, uPiece, uCode}
      PublicTarget) :
    CT2.LocalDeletionClosureRule
      (Target := CT1.Target profile.encoding.spec) profile.capability where
  preservesBaseline := profile.closure.preservesBaseline
  targetMonotone := by
    intro object state piece proper admissible baseline reducedTarget
    apply profile.encoding.bridge.target_of_publicTarget
    apply profile.closure.targetMonotone state piece proper admissible baseline
    exact profile.encoding.bridge.publicTarget_of_target reducedTarget

/-- Read the local avoiding residual from the complete certified CT1 run. -/
def currentAvoiding
    {P : Core.Problem.{uAmbient, uBranch}}
    {PublicTarget : P.Ambient → Prop}
    (profile : CertificateProfile.{uAmbient, uBranch, uPiece, uCode}
      PublicTarget)
    (ctx : Core.MinimalCounterexampleContext P PublicTarget)
    (previous : CT1.CertifiedAvoidingRun profile.encoding.spec
      (profile.input ctx)) :
    PackedAvoiding profile.encoding.spec (profile.input ctx) :=
  PackedAvoiding.ofResult previous.result previous.terminal_eq

/-- Exact complete CT1 run ledger consumed by the local transition. -/
def sourceLedger
    {P : Core.Problem.{uAmbient, uBranch}}
    {PublicTarget : P.Ambient → Prop}
    (profile : CertificateProfile.{uAmbient, uBranch, uPiece, uCode}
      PublicTarget)
    (ctx : Core.MinimalCounterexampleContext P PublicTarget) :
    Core.Routing.ResidualStage .ct1
      (CT1.CertifiedAvoidingRun profile.encoding.spec (profile.input ctx)) :=
  Core.Routing.ResidualStage.exact (profile.runAvoiding ctx)

/-- Framework-owned executable local-deletion transition. -/
abbrev transition
    {P : Core.Problem.{uAmbient, uBranch}}
    {PublicTarget : P.Ambient → Prop}
    (profile : CertificateProfile.{uAmbient, uBranch, uPiece, uCode}
      PublicTarget)
    (ctx : Core.MinimalCounterexampleContext P PublicTarget) :=
  LocalDeletion.transition profile.capability (profile.targetMinimality ctx)
    profile.routedClosure

/-- Exhaustive transition result retaining the complete CT1 source ledger. -/
def outcome
    {P : Core.Problem.{uAmbient, uBranch}}
    {PublicTarget : P.Ambient → Prop}
    (profile : CertificateProfile.{uAmbient, uBranch, uPiece, uCode}
      PublicTarget)
    (ctx : Core.MinimalCounterexampleContext P PublicTarget) :=
  LocalDeletion.advance profile.capability (profile.targetMinimality ctx)
    profile.routedClosure (profile.currentAvoiding ctx)
      (profile.sourceLedger ctx)

/-- The context presented to CT2, definitionally inherited from CT1. -/
abbrev routedContext
    {P : Core.Problem.{uAmbient, uBranch}}
    {PublicTarget : P.Ambient → Prop}
    (profile : CertificateProfile.{uAmbient, uBranch, uPiece, uCode}
      PublicTarget)
    (ctx : Core.MinimalCounterexampleContext P PublicTarget) :=
  CT1ToCT2.targetContext (profile.targetMinimality ctx)
    (profile.avoidingSource ctx)

/-- Minimality and the closure theorem rule out every enabled local-deletion
transition stage. -/
theorem transition_not_enabled
    {P : Core.Problem.{uAmbient, uBranch}}
    {PublicTarget : P.Ambient → Prop}
    (profile : CertificateProfile.{uAmbient, uBranch, uPiece, uCode}
      PublicTarget)
    (ctx : Core.MinimalCounterexampleContext P PublicTarget) :
    ∀ stage : ((profile.transition ctx).onLedger
        (profile.currentAvoiding ctx)).EnabledStage (profile.sourceLedger ctx),
      profile.outcome ctx ≠ .enabled stage :=
  advance_not_enabled_of_closure (profile.targetMinimality ctx)
    (profile.currentAvoiding ctx) (profile.sourceLedger ctx)
      profile.routedClosure

@[simp] theorem transition_profile_id
    {P : Core.Problem.{uAmbient, uBranch}}
    {PublicTarget : P.Ambient → Prop}
    (profile : CertificateProfile.{uAmbient, uBranch, uPiece, uCode}
      PublicTarget)
    (ctx : Core.MinimalCounterexampleContext P PublicTarget) :
    (profile.transition ctx).profileId = LocalDeletion.transitionId := rfl

end CertificateProfile

/-- Executable local-deletion profile contract for the CT1→CT2 family. -/
def transitionContract : Core.CTTransitionProfileContract where
  profileId := transitionId
  sourceTacticId := "CT1"
  targetTacticId := "CT2"
  sourceResidualKind := "CT1.residual.avoiding"
  targetExecutableInterface :=
    "StructuralExhaustion.CT2.LocalDeletionClosureRule.executableInterface"
  transitionConstructor :=
    "StructuralExhaustion.Routes.CT1ToCT2.LocalDeletion.transition"
  advanceExecutor :=
    "StructuralExhaustion.Routes.CT1ToCT2.LocalDeletion.advance"
  selectionClass := .priority
  semanticDiscovery := .capabilityDiscovery
  problemSpecificInputs := [.targetCapability, .minimalityKernel]

end StructuralExhaustion.Routes.CT1ToCT2.LocalDeletion
