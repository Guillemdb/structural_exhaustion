import StructuralExhaustion.CT1.Automation
import StructuralExhaustion.CT12.Automation

namespace StructuralExhaustion.Routes.CT1ToCT12

universe uAmbient uBranch uIndex uWitness uLedger
universe uState uPeeled uDemand uTier

/-- Stable identity of this transition profile. -/
def transitionId : String := "CT1.terminal.c1->CT12"

/-!
# CT1 realization to CT12 peeling

This transition preserves a successful CT1 certificate and the complete branch
context while materializing a CT12 loop state.  The relation between the
realized object and that loop state is necessarily problem-specific, so the
adapter must carry a proof of its declared `Evidence`; it cannot merely assert
that a transition is valid.
-/

/-- The semantic success retained at CT1's C1 terminal.  This is deliberately
proof-valued: routing may use the certified target theorem but cannot inspect
or enumerate its witness to manufacture downstream computational data. -/
abbrev PackedC1
    {P : Core.Problem.{uAmbient, uBranch}}
    (S : CT1.Spec.{uIndex, uWitness} P) (input : CT1.Input P) : Prop :=
  CT1.Target S input.context.G

namespace PackedC1

/-- Package one literal CT1 realization with the framework-certified target
equivalence. -/
def ofRealization
    {P : Core.Problem.{uAmbient, uBranch}}
    {S : CT1.Spec.{uIndex, uWitness} P} {input : CT1.Input P}
    (index : S.TestIndex) (witness : S.Witness input.context.G index)
    (realizes : S.Realizes input.context.G index witness) : PackedC1 S input :=
  ⟨index, witness, realizes⟩

/-- Extract the certified target from a complete CT1 result at its C1 leaf. -/
def ofResult
    {P : Core.Problem.{uAmbient, uBranch}}
    {S : CT1.Spec.{uIndex, uWitness} P} {input : CT1.Input P}
    (result : CT1.ExecutionResult S input)
    (terminal : result.terminal = .c1) : PackedC1 S input := by
  cases result with
  | mk terminalId path outcome =>
      cases outcome with
      | c1 certificate => exact certificate.target
      | avoiding state => cases terminal

/-- Read the target from the full framework-certified CT1 execution ledger. -/
def ofCertifiedRun
    {P : Core.Problem.{uAmbient, uBranch}}
    {S : CT1.Spec.{uIndex, uWitness} P} {input : CT1.Input P}
    (run : CT1.CertifiedC1Run S input) : PackedC1 S input :=
  ofResult run.result run.terminal_eq

theorem target
    {P : Core.Problem.{uAmbient, uBranch}}
    {S : CT1.Spec.{uIndex, uWitness} P} {input : CT1.Input P}
    (source : PackedC1 S input) : CT1.Target S input.context.G := source

end PackedC1

/-- Problem-semantic bridge from an exact CT1 success to a CT12 loop seed.
The adapter declares the evidence that makes the transition meaningful and
must prove it for every source certificate. -/
structure SemanticAdapter
    {P : Core.Problem.{uAmbient, uBranch}}
    {S : CT1.Spec.{uIndex, uWitness} P} {input : CT1.Input P}
    (targetCapability : CT12.Capability.{uAmbient, uBranch, uState,
      uPeeled, uDemand, uTier} P) where
  trigger : PackedC1 S input → CT12.Trigger targetCapability input.context
  Evidence : (source : PackedC1 S input) →
    CT12.Trigger targetCapability input.context → Prop
  evidence : (source : PackedC1 S input) → Evidence source (trigger source)

/-- Successful CT1 and CT12 share the whole branch context definitionally. -/
def targetContext
    {P : Core.Problem.{uAmbient, uBranch}}
    {S : CT1.Spec.{uIndex, uWitness} P} {input : CT1.Input P}
    (_source : PackedC1 S input) : Core.BranchContext P :=
  input.context

/-- Framework-owned executable CT1→CT12 transition.  The adapter supplies
only the problem-semantic loop seed; the transition kernel owns target
execution and exact predecessor transport. -/
def transition
    {P : Core.Problem.{uAmbient, uBranch}}
    {S : CT1.Spec.{uIndex, uWitness} P} {input : CT1.Input P}
    (targetCapability : CT12.Capability.{uAmbient, uBranch, uState,
      uPeeled, uDemand, uTier} P)
    (adapter : SemanticAdapter (S := S) (input := input) targetCapability) :
    Core.Routing.CTTransition .ct1 .ct12 (PackedC1 S input)
      targetCapability.executableInterface :=
  Core.Routing.CTTransition.ofTotalResidual transitionId targetContext
    adapter.trigger

/-- Execute CT12 from a literal CT1 success stage.  The enabled branch exposes
the full accumulated stage; subsequent transitions consume its `ledgerStage`. -/
def advance
    {P : Core.Problem.{uAmbient, uBranch}}
    {S : CT1.Spec.{uIndex, uWitness} P} {input : CT1.Input P}
    (targetCapability : CT12.Capability.{uAmbient, uBranch, uState,
      uPeeled, uDemand, uTier} P)
    (adapter : SemanticAdapter (S := S) (input := input) targetCapability)
    {Ledger : Sort uLedger} (current : Ledger → PackedC1 S input)
    (source : Core.Routing.ResidualStage .ct1 Ledger) :
    Core.Routing.ResidualStage .ct12
      (((transition targetCapability adapter).onLedger current).EnabledStage source) :=
  Core.Routing.CTTransition.runEnabledLedgerOnLedger
    (transition targetCapability adapter) current source () rfl

theorem branchContext_preserved
    {P : Core.Problem.{uAmbient, uBranch}}
    {S : CT1.Spec.{uIndex, uWitness} P} {input : CT1.Input P}
    (source : PackedC1 S input) : targetContext source = input.context := rfl

/-- The transition trigger retains the exact semantic bridge proved by the
adapter. -/
theorem evidence_preserved
    {P : Core.Problem.{uAmbient, uBranch}}
    {S : CT1.Spec.{uIndex, uWitness} P} {input : CT1.Input P}
    (targetCapability : CT12.Capability.{uAmbient, uBranch, uState,
      uPeeled, uDemand, uTier} P)
    (adapter : SemanticAdapter (S := S) (input := input) targetCapability)
    {Ledger : Sort uLedger} (current : Ledger → PackedC1 S input)
    (source : Core.Routing.ResidualStage .ct1 Ledger) :
    adapter.Evidence (current source.output)
      (((transition targetCapability adapter).onLedger current).trigger source ()) := by
  change adapter.Evidence (current source.output)
    (adapter.trigger (current source.output))
  exact adapter.evidence (current source.output)

/-- Forced execution is the target capability's canonical CT12 run. -/
theorem enabled_sound
    {P : Core.Problem.{uAmbient, uBranch}}
    {S : CT1.Spec.{uIndex, uWitness} P} {input : CT1.Input P}
    (targetCapability : CT12.Capability.{uAmbient, uBranch, uState,
      uPeeled, uDemand, uTier} P)
    (adapter : SemanticAdapter (S := S) (input := input) targetCapability)
    {Ledger : Sort uLedger} (current : Ledger → PackedC1 S input)
    (source : Core.Routing.ResidualStage .ct1 Ledger) :
    (advance targetCapability adapter current source).output.targetResult =
      targetCapability.executableInterface.execute
        (((transition targetCapability adapter).onLedger current).targetContext source)
        (((transition targetCapability adapter).onLedger current).trigger source ()) := rfl

@[simp] theorem source_tactic_id
    {P : Core.Problem.{uAmbient, uBranch}}
    {S : CT1.Spec.{uIndex, uWitness} P} {input : CT1.Input P}
    (targetCapability : CT12.Capability.{uAmbient, uBranch, uState,
      uPeeled, uDemand, uTier} P)
    (adapter : SemanticAdapter (S := S) (input := input) targetCapability) :
    (transition targetCapability adapter).sourceTacticId = "CT1" := rfl

@[simp] theorem target_tactic_id
    {P : Core.Problem.{uAmbient, uBranch}}
    {S : CT1.Spec.{uIndex, uWitness} P} {input : CT1.Input P}
    (targetCapability : CT12.Capability.{uAmbient, uBranch, uState,
      uPeeled, uDemand, uTier} P)
    (adapter : SemanticAdapter (S := S) (input := input) targetCapability) :
    (transition targetCapability adapter).targetTacticId = "CT12" := rfl

@[simp] theorem transition_profile_id
    {P : Core.Problem.{uAmbient, uBranch}}
    {S : CT1.Spec.{uIndex, uWitness} P} {input : CT1.Input P}
    (targetCapability : CT12.Capability.{uAmbient, uBranch, uState,
      uPeeled, uDemand, uTier} P)
    (adapter : SemanticAdapter (S := S) (input := input) targetCapability) :
    (transition targetCapability adapter).profileId = transitionId := rfl

/-- Machine-readable executable profile for the forced CT1→CT12 family. -/
def transitionContract : Core.CTTransitionProfileContract where
  profileId := transitionId
  sourceTacticId := "CT1"
  targetTacticId := "CT12"
  sourceResidualKind := "CT1.terminal.c1"
  targetExecutableInterface :=
    "StructuralExhaustion.CT12.Capability.executableInterface"
  transitionConstructor :=
    "StructuralExhaustion.Routes.CT1ToCT12.transition"
  advanceExecutor := "StructuralExhaustion.Routes.CT1ToCT12.advance"
  selectionClass := .forced
  semanticDiscovery := .problemSemanticAdapter
    "StructuralExhaustion.Routes.CT1ToCT12.SemanticAdapter"
  problemSpecificInputs := [.targetCapability, .semanticDiscoveryAdapter]

end StructuralExhaustion.Routes.CT1ToCT12
