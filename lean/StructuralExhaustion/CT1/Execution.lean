import StructuralExhaustion.CT1.Graph
import StructuralExhaustion.CT1.Search
import StructuralExhaustion.Core.CTTransition

namespace StructuralExhaustion.CT1

universe uAmbient uBranch uIndex uWitness

/-- Semantic terminal evidence, indexed by the exact CT1 terminal. -/
inductive RawOutcome {P : Core.Problem.{uAmbient, uBranch}}
    (S : Spec.{uIndex, uWitness} P) (input : Input P) :
    Graph.Terminal → Type (max (uIndex + 1) (uWitness + 1)) where
  | c1 {equivalence : EquivalenceState S input}
      (certificate : C1Certificate S input equivalence) :
      RawOutcome S input .c1
  | avoiding {equivalence : EquivalenceState S input}
      (state : AvoidingState S input equivalence) :
      RawOutcome S input .avoiding

/-- A CT1 result bundles one semantic terminal, the kernel-typed path reaching
it, and terminal evidence carrying the same index. -/
structure ExecutionResult {P : Core.Problem.{uAmbient, uBranch}}
    (S : Spec.{uIndex, uWitness} P)
    (input : Input P) : Type (max (uIndex + 1) (uWitness + 1)) where
  terminal : Graph.Terminal
  path : Graph.Path S input .entry terminal.nodeId
  outcome : RawOutcome S input terminal

namespace ExecutionResult

def trace {P : Core.Problem.{uAmbient, uBranch}}
    {S : Spec.{uIndex, uWitness} P} {input : Input P}
    (result : ExecutionResult S input) : List Graph.NodeId :=
  result.path.trace

end ExecutionResult

/-- The framework executes every CT1 node and constructs the exact path from
the capability primitives; the caller supplies no completed node decision. -/
def runReference {P : Core.Problem.{uAmbient, uBranch}}
    (S : Spec.{uIndex, uWitness} P) (capability : Capability S)
    (input : Input P) : ExecutionResult S input :=
  let equivalence := certifyEquivalence S input
  match findRealization S capability input equivalence with
  | .hit certificate => {
      terminal := .c1
      path := .cons .beginEquivalence
        (.cons (.equivalenceCertified equivalence)
          (.cons (.realizationHit certificate) (.nil .c1Terminal)))
      outcome := .c1 certificate
    }
  | .avoiding state => {
      terminal := .avoiding
      path := .cons .beginEquivalence
        (.cons (.equivalenceCertified equivalence)
          (.cons (.realizationAvoiding state) (.nil .avoidingTerminal)))
      outcome := .avoiding state
    }

/-- Public CT1 execution returns the exact path and matching terminal
evidence. Consumers can project `terminal` or `outcome` when they do not need
the trace. -/
def run {P : Core.Problem.{uAmbient, uBranch}}
    (S : Spec.{uIndex, uWitness} P) (capability : Capability S)
    (input : Input P) : ExecutionResult S input :=
  runReference S capability input

/-- Proposition established at each semantic terminal. -/
def OutcomeClaim {P : Core.Problem.{uAmbient, uBranch}}
    {S : Spec.{uIndex, uWitness} P} {input : Input P}
    {terminal : Graph.Terminal} : RawOutcome S input terminal → Prop
  | .c1 _ => Target S input.context.G
  | .avoiding _ => ¬ Target S input.context.G

namespace Capability

/-- Canonical executable CT1 entry.  A transition supplies only the inherited
branch context; the framework constructs the CT1 input and invokes the public
reference runner. -/
def executableInterface
    {P : Core.Problem.{uAmbient, uBranch}}
    {S : Spec.{uIndex, uWitness} P}
    (capability : Capability S) :
    Core.Routing.ExecutableInterface .ct1 where
  Context := Core.BranchContext P
  Trigger := fun _context => Unit
  Result := fun context _trigger => ExecutionResult S ⟨context⟩
  execute := fun context _trigger => run S capability ⟨context⟩

end Capability

end StructuralExhaustion.CT1
