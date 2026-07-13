import StructuralExhaustion.CT10.Graph

namespace StructuralExhaustion.CT10

universe uAmbient uBranch uDatum uClass uPromotion
variable {P : Core.Problem.{uAmbient, uBranch}}
variable (capability : Capability.{uAmbient, uBranch, uDatum, uClass, uPromotion} P)
variable (input : Input capability)

inductive Outcome : Graph.Terminal → Type _ where
  | direct (r : DirectResidual capability) : Outcome .direct
  | promoted (r : PromotedResidual capability input) : Outcome .promoted
  | exhaustive (c : ExhaustiveCertificate capability input) : Outcome .exhaustive

structure ExecutionResult where
  terminal : Graph.Terminal
  path : Graph.Path capability input .entry terminal.nodeId
  outcome : Outcome capability input terminal

namespace ExecutionResult
def trace (r : ExecutionResult capability input) := r.path.trace
end ExecutionResult

def runReference : ExecutionResult capability input :=
  match analyzeDirect capability with
  | .found residual => ⟨.direct,
      .cons .begin (.cons .tableBuilt
        (.cons (.directFound residual) (.nil .directTerminal))),
      .direct residual⟩
  | .absent directAbsent =>
      match analyzeMissing capability input directAbsent with
      | .promoted residual => ⟨.promoted,
          .cons .begin (.cons .tableBuilt
            (.cons (.directAbsent directAbsent)
              (.cons (.missingFound residual)
                (.cons (.promoted residual) (.nil .promotedTerminal))))),
          .promoted residual⟩
      | .exhaustive certificate => ⟨.exhaustive,
          .cons .begin (.cons .tableBuilt
            (.cons (.directAbsent directAbsent)
              (.cons (.exhaustive certificate) (.nil .exhaustiveTerminal)))),
          .exhaustive certificate⟩

def run : ExecutionResult capability input := runReference capability input

end StructuralExhaustion.CT10
