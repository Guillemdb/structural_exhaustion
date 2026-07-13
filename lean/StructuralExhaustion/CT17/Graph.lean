import StructuralExhaustion.CT17.Search

namespace StructuralExhaustion.CT17.Graph

open StructuralExhaustion.CT17

universe uAmbient uBranch uTarget uOffset uPosition uValue

inductive NodeId where
  | entry
  | compatibility
  | scale
  | survivors
  | arithmetic
  | incompatibilityTerminal
  | exhaustedTerminal
  | survivorTerminal
  | targetHitTerminal
  | orbitTerminal
  deriving Repr, DecidableEq

namespace NodeId

def code : NodeId → String
  | .entry => "CT17.entry"
  | .compatibility => "CT17.search.compatibility"
  | .scale => "CT17.decide.scale"
  | .survivors => "CT17.enumerate.survivors"
  | .arithmetic => "CT17.decide.arithmetic"
  | .incompatibilityTerminal => "CT17.terminal.residual.incompatibility"
  | .exhaustedTerminal => "CT17.terminal.certificate.exhausted"
  | .survivorTerminal => "CT17.terminal.residual.survivors"
  | .targetHitTerminal => "CT17.terminal.certificate.target-hit"
  | .orbitTerminal => "CT17.terminal.residual.orbit"

end NodeId

inductive Terminal where
  | incompatibility
  | exhausted
  | survivors
  | targetHit
  | orbit
  deriving Repr, DecidableEq

namespace Terminal

def nodeId : Terminal → NodeId
  | .incompatibility => .incompatibilityTerminal
  | .exhausted => .exhaustedTerminal
  | .survivors => .survivorTerminal
  | .targetHit => .targetHitTerminal
  | .orbit => .orbitTerminal

end Terminal

inductive Edge
    {P : Core.Problem.{uAmbient, uBranch}}
    (S : Spec.{uAmbient, uBranch, uTarget, uOffset, uPosition, uValue} P)
    (capability : Capability S)
    (ctx : Core.BranchContext P)
    (input : Input S capability ctx) : NodeId → NodeId → Type _ where
  | begin : Edge S capability ctx input .entry .compatibility
  | incompatible (residual : IncompatibilityResidual S capability ctx input) :
      Edge S capability ctx input .compatibility .incompatibilityTerminal
  | compatible (state : CompatibleState S capability ctx input) :
      Edge S capability ctx input .compatibility .scale
  | finite {compatible : CompatibleState S capability ctx input}
      (state : FiniteScaleState S capability ctx input compatible) :
      Edge S capability ctx input .scale .survivors
  | orbitScale {compatible : CompatibleState S capability ctx input}
      (state : OrbitScaleState S capability ctx input compatible) :
      Edge S capability ctx input .scale .arithmetic
  | exhausted {compatible : CompatibleState S capability ctx input}
      {finite : FiniteScaleState S capability ctx input compatible}
      (certificate : ExhaustedCertificate
        (S := S) (capability := capability) (ctx := ctx) (input := input)
        (compatible := compatible) (finite := finite)) :
      Edge S capability ctx input .survivors .exhaustedTerminal
  | survivors {compatible : CompatibleState S capability ctx input}
      {finite : FiniteScaleState S capability ctx input compatible}
      (residual : SurvivorResidual
        (S := S) (capability := capability) (ctx := ctx) (input := input)
        (compatible := compatible) (finite := finite)) :
      Edge S capability ctx input .survivors .survivorTerminal
  | targetHit {compatible : CompatibleState S capability ctx input}
      {orbit : OrbitScaleState S capability ctx input compatible}
      (certificate : TargetHitCertificate S capability ctx input orbit) :
      Edge S capability ctx input .arithmetic .targetHitTerminal
  | orbit {compatible : CompatibleState S capability ctx input}
      {orbitState : OrbitScaleState S capability ctx input compatible}
      (residual : OrbitResidual S capability ctx input orbitState) :
      Edge S capability ctx input .arithmetic .orbitTerminal

namespace Edge

def source
    {P : Core.Problem.{uAmbient, uBranch}}
    {S : Spec.{uAmbient, uBranch, uTarget, uOffset, uPosition, uValue} P}
    {capability : Capability S} {ctx : Core.BranchContext P}
    {input : Input S capability ctx} {first second : NodeId}
    (_edge : Edge S capability ctx input first second) : NodeId := first

end Edge

inductive Path
    {P : Core.Problem.{uAmbient, uBranch}}
    (S : Spec.{uAmbient, uBranch, uTarget, uOffset, uPosition, uValue} P)
    (capability : Capability S)
    (ctx : Core.BranchContext P)
    (input : Input S capability ctx) : NodeId → NodeId → Type _ where
  | nil (node : NodeId) : Path S capability ctx input node node
  | cons {first second last : NodeId} :
      Edge S capability ctx input first second →
      Path S capability ctx input second last →
      Path S capability ctx input first last

namespace Path

def trace
    {P : Core.Problem.{uAmbient, uBranch}}
    {S : Spec.{uAmbient, uBranch, uTarget, uOffset, uPosition, uValue} P}
    {capability : Capability S} {ctx : Core.BranchContext P}
    {input : Input S capability ctx} {first last : NodeId} :
    Path S capability ctx input first last → List NodeId
  | .nil node => [node]
  | .cons edge rest => edge.source :: rest.trace

end Path

def ValidTrace
    {P : Core.Problem.{uAmbient, uBranch}}
    {S : Spec.{uAmbient, uBranch, uTarget, uOffset, uPosition, uValue} P}
    {capability : Capability S} {ctx : Core.BranchContext P}
    {input : Input S capability ctx} (nodes : List NodeId) : Prop :=
  ∃ terminal : Terminal,
    ∃ path : Path S capability ctx input .entry terminal.nodeId,
      path.trace = nodes

end StructuralExhaustion.CT17.Graph
