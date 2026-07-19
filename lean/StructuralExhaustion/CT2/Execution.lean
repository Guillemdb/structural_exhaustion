import StructuralExhaustion.CT2.Graph
import StructuralExhaustion.Core.CTTransition

namespace StructuralExhaustion.CT2

universe uAmbient uBranch uPiece uInterface uAbstract uContext uCandidate

variable {P : Core.Problem.{uAmbient, uBranch}}
variable {Target : P.Ambient → Prop}
variable (capability : Capability.{uAmbient, uBranch, uPiece, uInterface,
  uAbstract, uContext, uCandidate} P Target)
variable (ctx : Core.MinimalCounterexampleContext P Target)
variable (input : Input capability ctx)

/-! Pure reference execution.  The framework, not a proof instance, constructs
every node result, graph edge, and trace. -/

inductive RawOutcome : Graph.Terminal → Type _ where
  | deletionC2
      (witness : DeletionWitness capability ctx input) :
      RawOutcome .deletionC2
  | replacementC2
      (witness : ReplacementWitness capability ctx input) :
      RawOutcome .replacementC2
  | separating
      (residual : SeparatingContextResidual capability ctx input) :
      RawOutcome .separating
  | criticality
      (residual : CriticalityResidual capability ctx input) :
      RawOutcome .criticality

structure ExecutionResult where
  terminal : Graph.Terminal
  path : Graph.Path capability ctx input .entry terminal.nodeId
  outcome : RawOutcome capability ctx input terminal

namespace ExecutionResult

def trace (result : ExecutionResult capability ctx input) : List Graph.NodeId :=
  result.path.trace

end ExecutionResult

/-- The canonical exhaustive CT2 interpreter. -/
def runReference : ExecutionResult capability ctx input :=
  match analyzeDeletion capability ctx input with
  | .closes witness => {
      terminal := .deletionC2
      path := .cons .beginDeletion
        (.cons (.deletionCloses witness) (.nil .deletionC2Terminal))
      outcome := .deletionC2 witness
    }
  | .critical deletionCritical =>
      match analyzeReplacements capability ctx input deletionCritical with
      | .closes witness => {
          terminal := .replacementC2
          path := .cons .beginDeletion
            (.cons (.deletionCritical deletionCritical)
              (.cons (.replacementCloses witness) (.nil .replacementC2Terminal)))
          outcome := .replacementC2 witness
        }
      | .separating residual => {
          terminal := .separating
          path := .cons .beginDeletion
            (.cons (.deletionCritical deletionCritical)
              (.cons (.replacementSeparating residual) (.nil .separatingTerminal)))
          outcome := .separating residual
        }
      | .critical residual => {
          terminal := .criticality
          path := .cons .beginDeletion
            (.cons (.deletionCritical deletionCritical)
              (.cons (.replacementCritical residual) (.nil .criticalityTerminal)))
          outcome := .criticality residual
        }

/-- The public runner is the audited reference semantics. -/
def run : ExecutionResult capability ctx input :=
  runReference capability ctx input

namespace Capability

/-- Canonical executable entry for the full CT2 replacement profile.  The
route chooses a seed through `Capability.discover`; execution consumes that
exact context-indexed input without rebuilding it in the application. -/
def executableInterface
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    (capability : Capability.{uAmbient, uBranch, uPiece, uInterface,
      uAbstract, uContext, uCandidate} P Target) :
    Core.Routing.ExecutableInterface .ct2 where
  Context := Core.MinimalCounterexampleContext P Target
  Trigger := Input capability
  Result := fun context input => ExecutionResult capability context input
  execute := fun context input => run capability context input

end Capability

end StructuralExhaustion.CT2
