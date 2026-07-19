import StructuralExhaustion.CT2.Graph
import StructuralExhaustion.Core.CTTransition

namespace StructuralExhaustion.CT2

universe uAmbient uBranch uPiece

/-!
# Local deletion closure

This execution surface is for the common minimal-counterexample step in which
one explicit proper admissible piece is deleted.  Baseline preservation and
target monotonicity determine the C2 witness directly; no target decision and
no search over ambient objects occurs.
-/

/-- The structural data needed by the local deletion rule. -/
structure LocalDeletionCapability (P : Core.Problem.{uAmbient, uBranch}) where
  pieces : PieceSystem.{uAmbient, uBranch, uPiece} P
  reductions : ReductionOps pieces

/-- One explicitly supplied local deletion seed. -/
structure LocalDeletionInput
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    (capability : LocalDeletionCapability.{uAmbient, uBranch, uPiece} P)
    (ctx : Core.MinimalCounterexampleContext P Target) where
  seed : Seed capability.pieces ctx

namespace LocalDeletionCapability

/-- Discover the first proper admissible local deletion piece using only the
declared finite piece schedule and its two primitive deciders. -/
def discover
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    (capability : LocalDeletionCapability.{uAmbient, uBranch, uPiece} P)
    (ctx : Core.MinimalCounterexampleContext P Target) :
    Core.Routing.Discovery (LocalDeletionInput capability ctx) :=
  match capability.pieces.discover ctx with
  | .enabled seed => .enabled ⟨seed⟩
  | .disabled reject => .disabled fun input => reject input.seed

end LocalDeletionCapability

/-- Semantic rule establishing that deletion preserves the counterexample
conditions whenever the supplied piece is proper and admissible. -/
structure LocalDeletionClosureRule
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    (capability : LocalDeletionCapability.{uAmbient, uBranch, uPiece} P) : Prop where
  preservesBaseline :
    ∀ {G : P.Ambient} (state : P.BranchState G)
      (piece : capability.pieces.Piece G),
      capability.pieces.Proper piece →
      capability.pieces.Admissible state piece →
      P.Baseline G →
      P.Baseline (capability.reductions.delete piece).value
  targetMonotone :
    ∀ {G : P.Ambient} (state : P.BranchState G)
      (piece : capability.pieces.Piece G),
      capability.pieces.Proper piece →
      capability.pieces.Admissible state piece →
      P.Baseline G →
      Target (capability.reductions.delete piece).value → Target G

/-- Exact local evidence that the deletion is a smaller counterexample. -/
structure LocalDeletionWitness
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    (capability : LocalDeletionCapability.{uAmbient, uBranch, uPiece} P)
    (ctx : Core.MinimalCounterexampleContext P Target)
    (input : LocalDeletionInput capability ctx) : Prop where
  baseline : P.Baseline
    (capability.reductions.delete input.seed.piece).value
  avoids : ¬ Target (capability.reductions.delete input.seed.piece).value

namespace LocalDeletionWitness

theorem contradiction
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    {capability : LocalDeletionCapability.{uAmbient, uBranch, uPiece} P}
    {ctx : Core.MinimalCounterexampleContext P Target}
    {input : LocalDeletionInput capability ctx}
    (witness : LocalDeletionWitness capability ctx input) : False :=
  Core.SmallerObject.counterexample_impossible ctx
    (capability.reductions.delete input.seed.piece)
    witness.baseline witness.avoids

end LocalDeletionWitness

/-- Typed edges of the local CT2 deletion path. -/
inductive LocalDeletionEdge
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    (capability : LocalDeletionCapability.{uAmbient, uBranch, uPiece} P)
    (ctx : Core.MinimalCounterexampleContext P Target)
    (input : LocalDeletionInput capability ctx) :
    Graph.NodeId → Graph.NodeId → Type _ where
  | beginDeletion : LocalDeletionEdge capability ctx input
      .entry .deletionDecision
  | deletionCloses (witness : LocalDeletionWitness capability ctx input) :
      LocalDeletionEdge capability ctx input
        .deletionDecision .deletionC2Terminal

namespace LocalDeletionEdge

def source
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    {capability : LocalDeletionCapability.{uAmbient, uBranch, uPiece} P}
    {ctx : Core.MinimalCounterexampleContext P Target}
    {input : LocalDeletionInput capability ctx}
    {first second : Graph.NodeId}
    (_edge : LocalDeletionEdge capability ctx input first second) :
    Graph.NodeId := first

end LocalDeletionEdge

inductive LocalDeletionPath
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    (capability : LocalDeletionCapability.{uAmbient, uBranch, uPiece} P)
    (ctx : Core.MinimalCounterexampleContext P Target)
    (input : LocalDeletionInput capability ctx) :
    Graph.NodeId → Graph.NodeId → Type _ where
  | nil (node : Graph.NodeId) :
      LocalDeletionPath capability ctx input node node
  | cons {first second last : Graph.NodeId} :
      LocalDeletionEdge capability ctx input first second →
      LocalDeletionPath capability ctx input second last →
      LocalDeletionPath capability ctx input first last

namespace LocalDeletionPath

def trace
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    {capability : LocalDeletionCapability.{uAmbient, uBranch, uPiece} P}
    {ctx : Core.MinimalCounterexampleContext P Target}
    {input : LocalDeletionInput capability ctx}
    {first last : Graph.NodeId} :
    LocalDeletionPath capability ctx input first last → List Graph.NodeId
  | .nil node => [node]
  | .cons edge rest => edge.source :: rest.trace

end LocalDeletionPath

/-- Complete proof-carrying local deletion execution. -/
structure LocalDeletionRun
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    (capability : LocalDeletionCapability.{uAmbient, uBranch, uPiece} P)
    (ctx : Core.MinimalCounterexampleContext P Target)
    (input : LocalDeletionInput capability ctx) where
  witness : LocalDeletionWitness capability ctx input
  path : LocalDeletionPath capability ctx input .entry .deletionC2Terminal
  checks : Nat
  checks_eq : checks = 1

namespace LocalDeletionRun

def terminal
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    {capability : LocalDeletionCapability.{uAmbient, uBranch, uPiece} P}
    {ctx : Core.MinimalCounterexampleContext P Target}
    {input : LocalDeletionInput capability ctx}
    (_run : LocalDeletionRun capability ctx input) : Graph.Terminal :=
  .deletionC2

def trace
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    {capability : LocalDeletionCapability.{uAmbient, uBranch, uPiece} P}
    {ctx : Core.MinimalCounterexampleContext P Target}
    {input : LocalDeletionInput capability ctx}
    (run : LocalDeletionRun capability ctx input) : List Graph.NodeId :=
  run.path.trace

theorem verified
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    {capability : LocalDeletionCapability.{uAmbient, uBranch, uPiece} P}
    {ctx : Core.MinimalCounterexampleContext P Target}
    {input : LocalDeletionInput capability ctx}
    (run : LocalDeletionRun capability ctx input) : False :=
  run.witness.contradiction

theorem checks_le
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    {capability : LocalDeletionCapability.{uAmbient, uBranch, uPiece} P}
    {ctx : Core.MinimalCounterexampleContext P Target}
    {input : LocalDeletionInput capability ctx}
    (run : LocalDeletionRun capability ctx input) : run.checks ≤ 1 := by
  simp [run.checks_eq]

end LocalDeletionRun

namespace LocalDeletionClosureRule

variable {P : Core.Problem.{uAmbient, uBranch}}
variable {Target : P.Ambient → Prop}
variable {capability : LocalDeletionCapability.{uAmbient, uBranch, uPiece} P}

def witness (rule : LocalDeletionClosureRule (Target := Target) capability)
    (ctx : Core.MinimalCounterexampleContext P Target)
    (input : LocalDeletionInput capability ctx) :
    LocalDeletionWitness capability ctx input where
  baseline := rule.preservesBaseline ctx.state input.seed.piece
    input.seed.proper input.seed.admissible ctx.baseline
  avoids := fun reducedTarget => ctx.avoids <|
    rule.targetMonotone ctx.state input.seed.piece input.seed.proper
      input.seed.admissible ctx.baseline reducedTarget

/-- Run the local deletion path without evaluating the target predicate. -/
def run (rule : LocalDeletionClosureRule (Target := Target) capability)
    (ctx : Core.MinimalCounterexampleContext P Target)
    (input : LocalDeletionInput capability ctx) :
    LocalDeletionRun capability ctx input where
  witness := rule.witness ctx input
  path := .cons .beginDeletion
    (.cons (.deletionCloses (rule.witness ctx input))
      (.nil .deletionC2Terminal))
  checks := 1
  checks_eq := rfl

/-- Canonical executable CT2 entry specialized to local deletion.  This is a
profile of the same `.ct2` interface used by the full replacement runner; its
smaller capability surface is retained in the trigger and result indices. -/
def executableInterface
    (rule : LocalDeletionClosureRule (Target := Target) capability) :
    Core.Routing.ExecutableInterface .ct2 where
  Context := Core.MinimalCounterexampleContext P Target
  Trigger := LocalDeletionInput capability
  Result := fun context input => LocalDeletionRun capability context input
  execute := fun context input => rule.run context input

theorem run_terminal
    (rule : LocalDeletionClosureRule (Target := Target) capability)
    (ctx : Core.MinimalCounterexampleContext P Target)
    (input : LocalDeletionInput capability ctx) :
    (rule.run ctx input).terminal = .deletionC2 := rfl

theorem run_trace
    (rule : LocalDeletionClosureRule (Target := Target) capability)
    (ctx : Core.MinimalCounterexampleContext P Target)
    (input : LocalDeletionInput capability ctx) :
    (rule.run ctx input).trace =
      [.entry, .deletionDecision, .deletionC2Terminal] := rfl

/-- A known admissible piece cannot be proper in a minimal counterexample. -/
theorem notProper
    (rule : LocalDeletionClosureRule (Target := Target) capability)
    (ctx : Core.MinimalCounterexampleContext P Target)
    (piece : capability.pieces.Piece ctx.G)
    (admissible : capability.pieces.Admissible ctx.state piece) :
    ¬ capability.pieces.Proper piece := by
  intro proper
  let input : LocalDeletionInput capability ctx :=
    ⟨⟨piece, proper, admissible⟩⟩
  exact (rule.run ctx input).verified

end LocalDeletionClosureRule

/-- Every explicit local deletion run has a constant degree-zero budget. -/
def localDeletionBudget
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    (capability : LocalDeletionCapability.{uAmbient, uBranch, uPiece} P)
    (ctx : Core.MinimalCounterexampleContext P Target) :
    Core.PolynomialCheckBudget (LocalDeletionInput capability ctx) :=
  Core.PolynomialCheckBudget.constant (fun _ => 1) 1

end StructuralExhaustion.CT2
