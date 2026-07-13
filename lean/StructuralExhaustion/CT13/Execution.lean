import StructuralExhaustion.CT13.Graph

namespace StructuralExhaustion.CT13

inductive RawOutcome {P : Core.Problem} (C : Capability P)
    (ctx : Core.BranchContext P) : Graph.Terminal → Type _ where
  | tierOne (r : TierOneResidual C ctx) : RawOutcome C ctx .tierOne
  | overlap (r : OverlapResidual C ctx) : RawOutcome C ctx .overlap
  | deficit (r : DeficitResidual C ctx) : RawOutcome C ctx .deficit
  | reconciled (c : ReconciliationCertificate C ctx) : RawOutcome C ctx .reconciled

structure ExecutionResult {P : Core.Problem} (C : Capability P)
    (ctx : Core.BranchContext P) where
  terminal : Graph.Terminal
  path : Graph.Path C ctx .entry terminal.nodeId
  outcome : RawOutcome C ctx terminal
namespace ExecutionResult
def trace {P : Core.Problem} {C : Capability P} {ctx : Core.BranchContext P}
    (result : ExecutionResult C ctx) := result.path.trace
end ExecutionResult

def runReference {P : Core.Problem} (C : Capability P) (ctx : Core.BranchContext P)
    (_input : Input C ctx) : ExecutionResult C ctx :=
  match selectTierOne C ctx with
  | .found residual => ⟨.tierOne,
      .cons .begin (.cons (.tierOne residual) (.nil .tierOneTerminal)),
      .tierOne residual⟩
  | .absent absence =>
      let fallback := computeFallback C ctx absence
      match reconcile C ctx fallback with
      | .overlap residual => ⟨.overlap,
          .cons .begin (.cons (.absent absence) (.cons (.fallback fallback)
            (.cons (.overlap residual) (.nil .overlapTerminal)))),
          .overlap residual⟩
      | .clean state =>
          match compare C ctx state with
          | .deficit residual => ⟨.deficit,
              .cons .begin (.cons (.absent absence) (.cons (.fallback fallback)
                (.cons (.clean state) (.cons (.deficit residual)
                  (.nil .deficitTerminal))))), .deficit residual⟩
          | .covers certificate => ⟨.reconciled,
              .cons .begin (.cons (.absent absence) (.cons (.fallback fallback)
                (.cons (.clean state) (.cons (.reconciled certificate)
                  (.nil .reconciledTerminal))))), .reconciled certificate⟩

def run {P : Core.Problem} (C : Capability P) (ctx : Core.BranchContext P)
    (input : Input C ctx) : ExecutionResult C ctx := runReference C ctx input

end StructuralExhaustion.CT13
