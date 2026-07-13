import StructuralExhaustion.CT3.Graph
import StructuralExhaustion.Core.SmallerObject

namespace StructuralExhaustion.CT3

universe uAmbient uBranch

/-!
# Certified literal compression

This is the CT3 execution surface for one replacement whose graph layer has
already derived a genuine smaller counterexample.  It owns only the typed CT3
path, the minimality contradiction, and the constant work certificate.  It
contains no boundaried-graph model and no whole-rank premise supplied by an
application: the graph profile must construct `Core.SmallerObject` itself.
-/

structure CertifiedCompressionInput
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    (ctx : Core.MinimalCounterexampleContext P Target) where
  reduction : Core.SmallerObject P ctx.G
  reducedBaseline : P.Baseline reduction.value
  targetMonotone : Target reduction.value → Target ctx.G

namespace CertifiedCompressionInput

def toCore
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    {ctx : Core.MinimalCounterexampleContext P Target}
    (input : CertifiedCompressionInput ctx) :
    Core.CertifiedReduction ctx where
  reduction := input.reduction
  reducedBaseline := input.reducedBaseline
  targetMonotone := input.targetMonotone

end CertifiedCompressionInput

structure CertifiedCompressionWitness
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    (ctx : Core.MinimalCounterexampleContext P Target)
    (input : CertifiedCompressionInput ctx) : Prop where
  baseline : P.Baseline input.reduction.value
  avoids : ¬ Target input.reduction.value

namespace CertifiedCompressionInput

def witness
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    {ctx : Core.MinimalCounterexampleContext P Target}
    (input : CertifiedCompressionInput ctx) :
    CertifiedCompressionWitness ctx input where
  baseline := input.toCore.witness.baseline
  avoids := input.toCore.witness.avoids

end CertifiedCompressionInput

namespace CertifiedCompressionWitness

theorem contradiction
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    {ctx : Core.MinimalCounterexampleContext P Target}
    {input : CertifiedCompressionInput ctx}
    (witness : CertifiedCompressionWitness ctx input) : False :=
  Core.SmallerObject.counterexample_impossible ctx input.reduction
    witness.baseline witness.avoids

end CertifiedCompressionWitness

inductive CertifiedCompressionEdge
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    (ctx : Core.MinimalCounterexampleContext P Target)
    (input : CertifiedCompressionInput ctx) :
    Graph.NodeId → Graph.NodeId → Type _ where
  | beginVector : CertifiedCompressionEdge ctx input
      .entry .vectorComputation
  | vectorReady : CertifiedCompressionEdge ctx input
      .vectorComputation .compressionSearch
  | compressionCloses (witness : CertifiedCompressionWitness ctx input) :
      CertifiedCompressionEdge ctx input
        .compressionSearch .compressionTerminal

namespace CertifiedCompressionEdge

def source
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    {ctx : Core.MinimalCounterexampleContext P Target}
    {input : CertifiedCompressionInput ctx}
    {first second : Graph.NodeId}
    (_edge : CertifiedCompressionEdge ctx input first second) : Graph.NodeId :=
  first

end CertifiedCompressionEdge

inductive CertifiedCompressionPath
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    (ctx : Core.MinimalCounterexampleContext P Target)
    (input : CertifiedCompressionInput ctx) :
    Graph.NodeId → Graph.NodeId → Type _ where
  | nil (node : Graph.NodeId) : CertifiedCompressionPath ctx input node node
  | cons {first second last : Graph.NodeId} :
      CertifiedCompressionEdge ctx input first second →
      CertifiedCompressionPath ctx input second last →
      CertifiedCompressionPath ctx input first last

namespace CertifiedCompressionPath

def trace
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    {ctx : Core.MinimalCounterexampleContext P Target}
    {input : CertifiedCompressionInput ctx}
    {first last : Graph.NodeId} :
    CertifiedCompressionPath ctx input first last → List Graph.NodeId
  | .nil node => [node]
  | .cons edge rest => edge.source :: rest.trace

end CertifiedCompressionPath

structure CertifiedCompressionRun
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    (ctx : Core.MinimalCounterexampleContext P Target)
    (input : CertifiedCompressionInput ctx) where
  witness : CertifiedCompressionWitness ctx input
  path : CertifiedCompressionPath ctx input .entry .compressionTerminal
  checks : Nat
  checks_eq : checks = 1

namespace CertifiedCompressionRun

def terminal
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    {ctx : Core.MinimalCounterexampleContext P Target}
    {input : CertifiedCompressionInput ctx}
    (_run : CertifiedCompressionRun ctx input) : Graph.Terminal :=
  .compression

def trace
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    {ctx : Core.MinimalCounterexampleContext P Target}
    {input : CertifiedCompressionInput ctx}
    (run : CertifiedCompressionRun ctx input) : List Graph.NodeId :=
  run.path.trace

theorem verified
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    {ctx : Core.MinimalCounterexampleContext P Target}
    {input : CertifiedCompressionInput ctx}
    (run : CertifiedCompressionRun ctx input) : False :=
  run.witness.contradiction

end CertifiedCompressionRun

def runCertifiedCompression
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    (ctx : Core.MinimalCounterexampleContext P Target)
    (input : CertifiedCompressionInput ctx) :
    CertifiedCompressionRun ctx input where
  witness := input.witness
  path := .cons .beginVector
    (.cons .vectorReady
      (.cons (.compressionCloses input.witness)
        (.nil .compressionTerminal)))
  checks := 1
  checks_eq := rfl

theorem runCertifiedCompression_terminal
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    (ctx : Core.MinimalCounterexampleContext P Target)
    (input : CertifiedCompressionInput ctx) :
    (runCertifiedCompression ctx input).terminal = .compression := rfl

theorem runCertifiedCompression_trace
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    (ctx : Core.MinimalCounterexampleContext P Target)
    (input : CertifiedCompressionInput ctx) :
    (runCertifiedCompression ctx input).trace =
      [.entry, .vectorComputation, .compressionSearch,
        .compressionTerminal] := rfl

theorem runCertifiedCompression_total
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    (ctx : Core.MinimalCounterexampleContext P Target)
    (input : CertifiedCompressionInput ctx) :
    ∃ run : CertifiedCompressionRun ctx input,
      run.terminal = .compression ∧
        run.trace = [.entry, .vectorComputation, .compressionSearch,
          .compressionTerminal] :=
  ⟨runCertifiedCompression ctx input, rfl, rfl⟩

def certifiedCompressionBudget
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    (ctx : Core.MinimalCounterexampleContext P Target) :
    Core.PolynomialCheckBudget (CertifiedCompressionInput ctx) :=
  Core.PolynomialCheckBudget.constant (fun _ => 1) 1

end StructuralExhaustion.CT3
