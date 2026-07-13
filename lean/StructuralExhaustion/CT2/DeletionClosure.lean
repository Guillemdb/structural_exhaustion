import StructuralExhaustion.Core.EnumerationCombinators
import StructuralExhaustion.CT2.Theorems

namespace StructuralExhaustion.CT2

universe uAmbient uBranch uPiece uInterface uAbstract uContext uCandidate

/-!
Reusable support for deletion-only CT2 instances.

The constructors in the first half remove representation boilerplate when a
piece is the whole ambient object, there is only one outside context, and no
replacement candidate is legal.  `DeletionClosureRule` is independent of
those constructors: it packages the two semantic preservation facts that
force deletion to close, then derives the CT2 witness, machine execution, and
discovery consequences.
-/

/-! The following dummy systems are intentionally private.  Replacement
analysis is uninhabited in a deletion-only capability, so their only role is
to fill the general dependent capability record. -/

private def deletionOnlyInterfaceSystem
    {P : Core.Problem.{uAmbient, uBranch}}
    (pieces : PieceSystem.{uAmbient, uBranch, uPiece} P) :
    InterfaceSystem pieces where
  Interface := Unit
  interface := fun _ => ()

private def deletionOnlyContextSystem
    {P : Core.Problem.{uAmbient, uBranch}}
    (pieces : PieceSystem.{uAmbient, uBranch, uPiece} P) :
    ContextSystem (deletionOnlyInterfaceSystem pieces) where
  AbstractPiece := fun _ => P.Ambient
  Context := fun _ => Unit
  contexts := fun _ => Core.Enumeration.unit
  glue := fun _ object => object
  abstract := fun {G} _ => G
  currentContext := fun _ => ()
  reconstruct := fun _ => rfl

private def deletionOnlyReplacementSystem
    {P : Core.Problem.{uAmbient, uBranch}}
    {pieces : PieceSystem.{uAmbient, uBranch, uPiece} P}
    {interfaces : InterfaceSystem.{uAmbient, uBranch, uPiece, uInterface} pieces}
    (contexts : ContextSystem.{uAmbient, uBranch, uPiece, uInterface,
      uAbstract, uContext} interfaces) : ReplacementSystem contexts where
  Candidate := fun _ => Empty
  candidates := fun _ => Core.Enumeration.empty
  replacement := fun _ candidate => nomatch candidate
  decreases := fun _ candidate => nomatch candidate

namespace Capability

/-- Assemble a deletion-only capability from its actual problem data.  The
unit interface, identity context, and empty replacement system are framework
defaults rather than author obligations. -/
def deletionOnly
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    (pieces : PieceSystem.{uAmbient, uBranch, uPiece} P)
    (observable : Observable P Target)
  (reductions : ReductionOps pieces) :
    Capability.{uAmbient, uBranch, uPiece, 0, uAmbient, 0, 0} P Target where
  pieces := pieces
  observable := observable
  reductions := reductions
  interfaces := deletionOnlyInterfaceSystem pieces
  contexts := deletionOnlyContextSystem pieces
  replacements := deletionOnlyReplacementSystem
    (deletionOnlyContextSystem pieces)

end Capability

/-- Semantic conditions under which every admitted CT2 seed closes through
deletion.  Both facts are stated before any node executes: baseline survives
the reduction, and the target is monotone back to the source object. -/
structure DeletionClosureRule
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    (capability : Capability.{uAmbient, uBranch, uPiece, uInterface,
      uAbstract, uContext, uCandidate} P Target) : Prop where
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

namespace DeletionClosureRule

variable {P : Core.Problem.{uAmbient, uBranch}}
variable {Target : P.Ambient → Prop}
variable {capability : Capability.{uAmbient, uBranch, uPiece, uInterface,
  uAbstract, uContext, uCandidate} P Target}

/-- Construct the deletion-C2 witness solely from the static closure rule and
the discovered seed. -/
def witness (rule : DeletionClosureRule capability)
    (ctx : Core.MinimalCounterexampleContext P Target)
    (input : Input capability ctx) : DeletionWitness capability ctx input where
  baseline := rule.preservesBaseline ctx.state input.seed.piece
    input.seed.proper input.seed.admissible ctx.baseline
  avoids := fun reducedTarget => ctx.avoids <|
    rule.targetMonotone ctx.state input.seed.piece input.seed.proper
      input.seed.admissible ctx.baseline reducedTarget

/-- Deletion analysis must select its closing branch whenever a static
deletion closure rule is available. -/
theorem analyzeDeletion_closes (rule : DeletionClosureRule capability)
    (ctx : Core.MinimalCounterexampleContext P Target)
    (input : Input capability ctx) :
    ∃ deletionWitness : DeletionWitness capability ctx input,
      analyzeDeletion capability ctx input = .closes deletionWitness := by
  cases decision : analyzeDeletion capability ctx input with
  | closes deletionWitness => exact ⟨deletionWitness, rfl⟩
  | critical critical =>
      exact (critical.notCounterexample
        ⟨(rule.witness ctx input).baseline,
          (rule.witness ctx input).avoids⟩).elim

/-- The canonical CT2 runner reaches the deletion-C2 terminal. -/
theorem run_terminal_deletionC2 (rule : DeletionClosureRule capability)
    (ctx : Core.MinimalCounterexampleContext P Target)
    (input : Input capability ctx) :
    (run capability ctx input).terminal = .deletionC2 := by
  obtain ⟨deletionWitness, closes⟩ := rule.analyzeDeletion_closes ctx input
  simp [run, runReference, closes]

/-- The same closure rule determines the complete deletion-C2 audit trace. -/
theorem run_trace_deletionC2 (rule : DeletionClosureRule capability)
    (ctx : Core.MinimalCounterexampleContext P Target)
    (input : Input capability ctx) :
    (run capability ctx input).trace =
      [.entry, .deletionDecision, .deletionC2Terminal] := by
  obtain ⟨deletionWitness, closes⟩ := rule.analyzeDeletion_closes ctx input
  simp only [run]
  unfold runReference
  rw [closes]
  rfl

end DeletionClosureRule

/-- Exact reference-run package for a deletion-only C2 closure. -/
structure DeletionC2Run
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    (capability : Capability.{uAmbient, uBranch, uPiece,
    uInterface, uAbstract, uContext, uCandidate} P Target)
    (ctx : Core.MinimalCounterexampleContext P Target)
    (input : Input capability ctx) where
  terminal_eq : (run capability ctx input).terminal = .deletionC2
  trace_eq : (run capability ctx input).trace =
    [.entry, .deletionDecision, .deletionC2Terminal]

namespace DeletionC2Run

variable {P : Core.Problem.{uAmbient, uBranch}}
variable {Target : P.Ambient → Prop}
variable {capability : Capability.{uAmbient, uBranch, uPiece, uInterface,
  uAbstract, uContext, uCandidate} P Target}
variable {ctx : Core.MinimalCounterexampleContext P Target}
variable {input : Input capability ctx}

def execution (_bundle : DeletionC2Run capability ctx input) :
    ExecutionResult capability ctx input :=
  run capability ctx input

/-- The witness is extracted from the outcome of this exact run. -/
def witness (bundle : DeletionC2Run capability ctx input) :
    DeletionWitness capability ctx input :=
  ExecutionResult.deletionWitness_of_terminal_eq capability ctx input
    bundle.execution bundle.terminal_eq

end DeletionC2Run

namespace DeletionClosureRule

variable {P : Core.Problem.{uAmbient, uBranch}}
variable {Target : P.Ambient → Prop}
variable {capability : Capability.{uAmbient, uBranch, uPiece, uInterface,
  uAbstract, uContext, uCandidate} P Target}

/-- Package the exact deletion-C2 execution generated by the closure rule. -/
def runDeletionC2 (rule : DeletionClosureRule capability)
    (ctx : Core.MinimalCounterexampleContext P Target)
    (input : Input capability ctx) : DeletionC2Run capability ctx input where
  terminal_eq := rule.run_terminal_deletionC2 ctx input
  trace_eq := rule.run_trace_deletionC2 ctx input

/-- Semantic verification of the actual dependent run turns an admitted seed
into the minimality contradiction certified by deletion-C2. -/
theorem run_closes (rule : DeletionClosureRule capability)
    (ctx : Core.MinimalCounterexampleContext P Target)
    (input : Input capability ctx) : False := by
  let result := run capability ctx input
  have reaches : result.terminal = .deletionC2 :=
    rule.run_terminal_deletionC2 ctx input
  have valid := result.verified
  rcases result with ⟨terminal, path, outcome⟩
  cases outcome with
  | deletionC2 _ => exact valid
  | replacementC2 _ => exact valid
  | separating _ => cases reaches
  | criticality _ => cases reaches

/-- If every admitted seed closes, exhaustive capability discovery is
necessarily disabled and returns its exact rejection function. -/
theorem discover_disabled (rule : DeletionClosureRule capability)
    (ctx : Core.MinimalCounterexampleContext P Target) :
    ∃ reject, capability.discover ctx = .disabled reject := by
  cases discovery : capability.discover ctx with
  | enabled input => exact (rule.run_closes ctx input).elim
  | disabled reject => exact ⟨reject, rfl⟩

/-- A piece known to be admissible cannot be proper in a minimal
counterexample: otherwise it would be an admitted deletion-closing seed. -/
theorem notProper (rule : DeletionClosureRule capability)
    (ctx : Core.MinimalCounterexampleContext P Target)
    (piece : capability.pieces.Piece ctx.G)
    (admissible : capability.pieces.Admissible ctx.state piece) :
    ¬ capability.pieces.Proper piece := by
  obtain ⟨reject, _disabled⟩ := rule.discover_disabled ctx
  intro proper
  exact reject ⟨⟨piece, proper, admissible⟩⟩

end DeletionClosureRule

end StructuralExhaustion.CT2
