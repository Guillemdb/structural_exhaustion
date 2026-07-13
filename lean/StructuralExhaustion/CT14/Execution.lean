import StructuralExhaustion.CT14.Graph

namespace StructuralExhaustion.CT14

inductive RawOutcome {P : Core.Problem} (C : Capability P)
    (ctx : Core.BranchContext P) : Graph.Terminal → Type _ where
  | unbounded (r : UnboundedMemberResidual C ctx) : RawOutcome C ctx .unbounded
  | missingLabel (r : MissingLabelResidual C ctx) : RawOutcome C ctx .missingLabel
  | aggregate (c : AggregateCertificate C ctx) : RawOutcome C ctx .aggregate
  | capacity (r : CapacityResidual C ctx) : RawOutcome C ctx .capacity

structure ExecutionResult {P : Core.Problem} (C : Capability P)
    (ctx : Core.BranchContext P) where
  terminal : Graph.Terminal
  path : Graph.Path C ctx .entry terminal.nodeId
  outcome : RawOutcome C ctx terminal
namespace ExecutionResult
def trace {P : Core.Problem} {C : Capability P} {ctx : Core.BranchContext P}
    (r : ExecutionResult C ctx) := r.path.trace
end ExecutionResult

def runReference {P : Core.Problem} (C : Capability P) (ctx : Core.BranchContext P)
    (_input : Input C ctx) : ExecutionResult C ctx :=
  let lower : LowerMassState C ctx := ⟨lowerMass C ctx, rfl⟩
  match scanMembers C ctx lower with
  | .unbounded residual => ⟨.unbounded,
      .cons .begin (.cons (.lower lower)
        (.cons (.unbounded residual) (.nil .unboundedTerminal))),
      .unbounded residual⟩
  | .missingLabel residual => ⟨.missingLabel,
      .cons .begin (.cons (.lower lower)
        (.cons (.missingLabel residual) (.nil .missingLabelTerminal))),
      .missingLabel residual⟩
  | .complete scan =>
      let ledger := computeLedger C ctx scan
      match compare C ctx ledger with
      | .exceeds certificate => ⟨.aggregate,
          .cons .begin (.cons (.lower lower) (.cons (.complete scan)
            (.cons (.upper ledger) (.cons (.aggregate certificate)
              (.nil .aggregateTerminal))))), .aggregate certificate⟩
      | .within residual => ⟨.capacity,
          .cons .begin (.cons (.lower lower) (.cons (.complete scan)
            (.cons (.upper ledger) (.cons (.capacity residual)
              (.nil .capacityTerminal))))), .capacity residual⟩

def run {P : Core.Problem} (C : Capability P) (ctx : Core.BranchContext P)
    (input : Input C ctx) : ExecutionResult C ctx := runReference C ctx input

end StructuralExhaustion.CT14
