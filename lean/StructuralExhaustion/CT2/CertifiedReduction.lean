import StructuralExhaustion.CT2.Graph

namespace StructuralExhaustion.CT2

universe uAmbient uBranch

/-!
# Certificate-driven local reduction

This CT2 surface closes one explicitly supplied smaller counterexample.  It is
the local alternative to `PieceSystem` discovery when the mathematical proof
already names the reduced object, as happens for an arbitrary proper
subobject.  The runner inspects no ambient-object universe and performs no
recursive search.
-/

/-- Complete local input for one known smaller reduction.  The source context
supplies target avoidance; the input supplies the reduced baseline and the
one-way target transport proved by the problem's structural layer. -/
structure CertifiedReductionInput
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    (ctx : Core.MinimalCounterexampleContext P Target) where
  reduction : Core.SmallerObject P ctx.G
  reducedBaseline : P.Baseline reduction.value
  targetMonotone : Target reduction.value → Target ctx.G

namespace CertifiedReductionInput

/-- Forget the CT2 execution surface and retain the shared minimality
certificate. -/
def toCore
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    {ctx : Core.MinimalCounterexampleContext P Target}
    (input : CertifiedReductionInput ctx) :
    Core.CertifiedReduction ctx where
  reduction := input.reduction
  reducedBaseline := input.reducedBaseline
  targetMonotone := input.targetMonotone

end CertifiedReductionInput

/-- Route-facing type contract for a supplied certified reduction. -/
def certifiedReductionTacticInterface
    (P : Core.Problem.{uAmbient, uBranch})
    (Target : P.Ambient → Prop) : Core.Routing.TacticInterface where
  Context := Core.MinimalCounterexampleContext P Target
  Trigger := CertifiedReductionInput

/-- Exact semantic evidence carried by the deletion-C2 edge. -/
structure CertifiedReductionWitness
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    (ctx : Core.MinimalCounterexampleContext P Target)
    (input : CertifiedReductionInput ctx) : Prop where
  baseline : P.Baseline input.reduction.value
  avoids : ¬ Target input.reduction.value

namespace CertifiedReductionWitness

theorem contradiction
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    {ctx : Core.MinimalCounterexampleContext P Target}
    {input : CertifiedReductionInput ctx}
    (witness : CertifiedReductionWitness ctx input) : False := by
  exact Core.SmallerObject.counterexample_impossible ctx input.reduction
    witness.baseline witness.avoids

end CertifiedReductionWitness

namespace CertifiedReductionInput

def witness
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    {ctx : Core.MinimalCounterexampleContext P Target}
    (input : CertifiedReductionInput ctx) :
    CertifiedReductionWitness ctx input where
  baseline := input.toCore.witness.baseline
  avoids := input.toCore.witness.avoids

end CertifiedReductionInput

/-! The CT2 graph path below is specialized to the certificate surface.  Its
node identifiers are the canonical CT2 deletion nodes. -/

/-- Typed edges for a certificate-driven deletion-C2 execution. -/
inductive CertifiedReductionEdge
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    (ctx : Core.MinimalCounterexampleContext P Target)
    (input : CertifiedReductionInput ctx) :
    Graph.NodeId → Graph.NodeId → Type _ where
  | beginDeletion : CertifiedReductionEdge ctx input
      .entry .deletionDecision
  | deletionCloses (witness : CertifiedReductionWitness ctx input) :
      CertifiedReductionEdge ctx input
        .deletionDecision .deletionC2Terminal

namespace CertifiedReductionEdge

def source
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    {ctx : Core.MinimalCounterexampleContext P Target}
    {input : CertifiedReductionInput ctx}
    {first second : Graph.NodeId}
    (_edge : CertifiedReductionEdge ctx input first second) : Graph.NodeId :=
  first

end CertifiedReductionEdge

/-- Typed canonical CT2 path for one certificate-driven reduction. -/
inductive CertifiedReductionPath
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    (ctx : Core.MinimalCounterexampleContext P Target)
    (input : CertifiedReductionInput ctx) :
    Graph.NodeId → Graph.NodeId → Type _ where
  | nil (node : Graph.NodeId) :
      CertifiedReductionPath ctx input node node
  | cons {first second last : Graph.NodeId} :
      CertifiedReductionEdge ctx input first second →
      CertifiedReductionPath ctx input second last →
      CertifiedReductionPath ctx input first last

namespace CertifiedReductionPath

def trace
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    {ctx : Core.MinimalCounterexampleContext P Target}
    {input : CertifiedReductionInput ctx}
    {first last : Graph.NodeId} :
    CertifiedReductionPath ctx input first last → List Graph.NodeId
  | .nil node => [node]
  | .cons edge rest => edge.source :: rest.trace

end CertifiedReductionPath

/-- Complete framework execution for one explicitly certified reduction. -/
structure CertifiedReductionRun
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    (ctx : Core.MinimalCounterexampleContext P Target)
    (input : CertifiedReductionInput ctx) where
  witness : CertifiedReductionWitness ctx input
  path : CertifiedReductionPath ctx input .entry .deletionC2Terminal
  checks : Nat
  checks_eq : checks = 1

namespace CertifiedReductionRun

def terminal
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    {ctx : Core.MinimalCounterexampleContext P Target}
    {input : CertifiedReductionInput ctx}
    (_run : CertifiedReductionRun ctx input) : Graph.Terminal :=
  .deletionC2

def trace
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    {ctx : Core.MinimalCounterexampleContext P Target}
    {input : CertifiedReductionInput ctx}
    (run : CertifiedReductionRun ctx input) : List Graph.NodeId :=
  run.path.trace

/-- Semantic soundness: a certified reduction contradicts the inherited
minimal-counterexample kernel. -/
theorem verified
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    {ctx : Core.MinimalCounterexampleContext P Target}
    {input : CertifiedReductionInput ctx}
    (run : CertifiedReductionRun ctx input) : False :=
  run.witness.contradiction

theorem checks_le
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    {ctx : Core.MinimalCounterexampleContext P Target}
    {input : CertifiedReductionInput ctx}
    (run : CertifiedReductionRun ctx input) : run.checks ≤ 1 := by
  simp [run.checks_eq]

end CertifiedReductionRun

/-- Public CT2 runner for one known local reduction. -/
def runCertifiedReduction
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    (ctx : Core.MinimalCounterexampleContext P Target)
    (input : CertifiedReductionInput ctx) :
    CertifiedReductionRun ctx input where
  witness := input.witness
  path := .cons .beginDeletion
    (.cons (.deletionCloses input.witness) (.nil .deletionC2Terminal))
  checks := 1
  checks_eq := rfl

theorem runCertifiedReduction_terminal
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    (ctx : Core.MinimalCounterexampleContext P Target)
    (input : CertifiedReductionInput ctx) :
    (runCertifiedReduction ctx input).terminal = .deletionC2 := rfl

theorem runCertifiedReduction_trace
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    (ctx : Core.MinimalCounterexampleContext P Target)
    (input : CertifiedReductionInput ctx) :
    (runCertifiedReduction ctx input).trace =
      [.entry, .deletionDecision, .deletionC2Terminal] := rfl

/-- Totality of the certificate-driven runner with its exact typed terminal
and trace. -/
theorem runCertifiedReduction_total
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    (ctx : Core.MinimalCounterexampleContext P Target)
    (input : CertifiedReductionInput ctx) :
    ∃ run : CertifiedReductionRun ctx input,
      run.terminal = .deletionC2 ∧
        run.trace = [.entry, .deletionDecision, .deletionC2Terminal] := by
  exact ⟨runCertifiedReduction ctx input, rfl, rfl⟩

/-- Every certificate-driven CT2 reduction has a constant degree-zero work
bound. -/
def certifiedReductionBudget
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    (ctx : Core.MinimalCounterexampleContext P Target) :
    Core.PolynomialCheckBudget (CertifiedReductionInput ctx) :=
  Core.PolynomialCheckBudget.constant (fun _ => 1) 1

end StructuralExhaustion.CT2
