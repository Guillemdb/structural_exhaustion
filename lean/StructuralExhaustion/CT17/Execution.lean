import StructuralExhaustion.CT17.Graph

namespace StructuralExhaustion.CT17

universe uAmbient uBranch uTarget uOffset uPosition uValue

variable {P : Core.Problem.{uAmbient, uBranch}}
variable (S : Spec.{uAmbient, uBranch, uTarget, uOffset, uPosition, uValue} P)
variable (capability : Capability S)
variable (ctx : Core.BranchContext P)
variable (input : Input S capability ctx)

inductive RawOutcome : Graph.Terminal → Type _ where
  | incompatibility (residual : IncompatibilityResidual S capability ctx input) :
      RawOutcome .incompatibility
  | exhausted {compatible : CompatibleState S capability ctx input}
      {finite : FiniteScaleState S capability ctx input compatible}
      (certificate : ExhaustedCertificate
        (S := S) (capability := capability) (ctx := ctx) (input := input)
        (compatible := compatible) (finite := finite)) :
      RawOutcome .exhausted
  | survivors {compatible : CompatibleState S capability ctx input}
      {finite : FiniteScaleState S capability ctx input compatible}
      (residual : SurvivorResidual
        (S := S) (capability := capability) (ctx := ctx) (input := input)
        (compatible := compatible) (finite := finite)) :
      RawOutcome .survivors
  | targetHit {compatible : CompatibleState S capability ctx input}
      {orbit : OrbitScaleState S capability ctx input compatible}
      (certificate : TargetHitCertificate S capability ctx input orbit) :
      RawOutcome .targetHit
  | orbit {compatible : CompatibleState S capability ctx input}
      {orbitState : OrbitScaleState S capability ctx input compatible}
      (residual : OrbitResidual S capability ctx input orbitState) :
      RawOutcome .orbit

structure ExecutionResult where
  terminal : Graph.Terminal
  path : Graph.Path S capability ctx input .entry terminal.nodeId
  outcome : RawOutcome S capability ctx input terminal

namespace ExecutionResult

def trace (result : ExecutionResult S capability ctx input) : List Graph.NodeId :=
  result.path.trace

end ExecutionResult

def runReference : ExecutionResult S capability ctx input :=
  match analyzeCompatibility S capability ctx input with
  | .incompatible residual =>
      ⟨.incompatibility,
        .cons .begin (.cons (.incompatible residual)
          (.nil .incompatibilityTerminal)),
        .incompatibility residual⟩
  | .compatible compatible =>
      match analyzeScale S capability ctx input compatible with
      | .finite finite =>
          match analyzeSurvivors S capability ctx input finite with
          | .exhausted certificate =>
              ⟨.exhausted,
                .cons .begin (.cons (.compatible compatible)
                  (.cons (.finite finite) (.cons (.exhausted certificate)
                    (.nil .exhaustedTerminal)))),
                .exhausted certificate⟩
          | .survivors residual =>
              ⟨.survivors,
                .cons .begin (.cons (.compatible compatible)
                  (.cons (.finite finite) (.cons (.survivors residual)
                    (.nil .survivorTerminal)))),
                .survivors residual⟩
      | .orbit orbit =>
          match analyzeArithmetic S capability ctx input orbit with
          | .targetHit certificate =>
              ⟨.targetHit,
                .cons .begin (.cons (.compatible compatible)
                  (.cons (.orbitScale orbit) (.cons (.targetHit certificate)
                    (.nil .targetHitTerminal)))),
                .targetHit certificate⟩
          | .residual residual =>
              ⟨.orbit,
                .cons .begin (.cons (.compatible compatible)
                  (.cons (.orbitScale orbit) (.cons (.orbit residual)
                    (.nil .orbitTerminal)))),
                .orbit residual⟩

def run : ExecutionResult S capability ctx input :=
  runReference S capability ctx input

end StructuralExhaustion.CT17
