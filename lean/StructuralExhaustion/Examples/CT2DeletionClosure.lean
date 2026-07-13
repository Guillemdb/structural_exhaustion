import StructuralExhaustion.Examples.CT2AutomationFirst

namespace StructuralExhaustion.Examples.CT2DeletionClosure

open StructuralExhaustion
open CT2AutomationFirst

/-! Kernel fixtures for the deletion-only constructors and closure rule. -/

abbrev deletionOnlyCapability : CT2.Capability problem target :=
  CT2.Capability.deletionOnly pieces observable reductions

def deletionOnlyInput : CT2.Input deletionOnlyCapability context where
  seed := {
    piece := .large
    proper := trivial
    admissible := trivial
  }

example :
    (deletionOnlyCapability.replacements.candidates
      deletionOnlyInput.seed.piece).orderedValues = [] :=
  rfl

example : (CT2.run deletionOnlyCapability context deletionOnlyInput).terminal =
    .criticality :=
  rfl

section ClosureRuleSurface

universe uAmbient uBranch uPiece uInterface uAbstract uContext uCandidate

variable {P : Core.Problem.{uAmbient, uBranch}}
variable {Target : P.Ambient → Prop}
variable {capability : CT2.Capability.{uAmbient, uBranch, uPiece, uInterface,
  uAbstract, uContext, uCandidate} P Target}
variable (rule : CT2.DeletionClosureRule capability)
variable (ctx : Core.MinimalCounterexampleContext P Target)
variable (input : CT2.Input capability ctx)

example : CT2.DeletionWitness capability ctx input :=
  rule.witness ctx input

example : (CT2.run capability ctx input).terminal = .deletionC2 :=
  rule.run_terminal_deletionC2 ctx input

example : (CT2.run capability ctx input).trace =
    [.entry, .deletionDecision, .deletionC2Terminal] :=
  rule.run_trace_deletionC2 ctx input

def exactRun : CT2.DeletionC2Run capability ctx input :=
  rule.runDeletionC2 ctx input

example : CT2.DeletionWitness capability ctx input :=
  (exactRun rule ctx input).witness

example : ∃ reject, capability.discover ctx = .disabled reject :=
  rule.discover_disabled ctx

example (piece : capability.pieces.Piece ctx.G)
    (admissible : capability.pieces.Admissible ctx.state piece) :
    ¬ capability.pieces.Proper piece :=
  rule.notProper ctx piece admissible

end ClosureRuleSurface

end StructuralExhaustion.Examples.CT2DeletionClosure
