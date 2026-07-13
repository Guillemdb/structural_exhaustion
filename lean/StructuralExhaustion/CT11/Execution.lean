import StructuralExhaustion.CT11.Graph

namespace StructuralExhaustion.CT11

universe uAmbient uBranch uCell
variable {P : Core.Problem.{uAmbient, uBranch}}
variable (capability : Capability.{uAmbient, uBranch, uCell} P)
variable (input : Input capability)

inductive Outcome : Graph.Terminal → Type _ where
  | gap (r : AdmissibilityGapResidual capability input) : Outcome .gap
  | localized (r : LocalizedDeficitResidual capability input) : Outcome .localized

structure ExecutionResult where
  terminal : Graph.Terminal
  path : Graph.Path capability input .entry terminal.nodeId
  outcome : Outcome capability input terminal

namespace ExecutionResult
def trace (r : ExecutionResult capability input) := r.path.trace
end ExecutionResult

def runReference : ExecutionResult capability input :=
  match analyzeAdmissibility capability input with
  | .gap residual => ⟨.gap,
      .cons .begin (.cons .decomposed
        (.cons (.gap residual) (.nil .gapTerminal))), .gap residual⟩
  | .closed admissible =>
      let residual := localize capability input admissible
      ⟨.localized, .cons .begin (.cons .decomposed
        (.cons (.closed admissible)
          (.cons (.localized residual) (.nil .localizedTerminal)))),
        .localized residual⟩

def run : ExecutionResult capability input := runReference capability input

end StructuralExhaustion.CT11
