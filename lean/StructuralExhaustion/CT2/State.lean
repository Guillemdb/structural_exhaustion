import StructuralExhaustion.CT2.Capability

namespace StructuralExhaustion.CT2

universe uAmbient uBranch uPiece uInterface uAbstract uContext uCandidate

variable {P : Core.Problem.{uAmbient, uBranch}}
variable {Target : P.Ambient → Prop}
variable (capability : Capability.{uAmbient, uBranch, uPiece, uInterface,
  uAbstract, uContext, uCandidate} P Target)
variable (ctx : Core.MinimalCounterexampleContext P Target)
variable (input : Input capability ctx)

/-! Exact predecessor-indexed evidence produced by the CT2 reference nodes. -/

/-- Reconstruct the source piece in an arbitrary compatible context. -/
def sourceObject
    (context : capability.contexts.Context
      (capability.interfaces.interface input.seed.piece)) : P.Ambient :=
  capability.contexts.glue context
    (capability.contexts.abstract input.seed.piece)

/-- Glue a legal replacement into an arbitrary compatible context. -/
def replacementObject
    (candidate : capability.replacements.Candidate input.seed.piece)
    (context : capability.contexts.Context
      (capability.interfaces.interface input.seed.piece)) : P.Ambient :=
  capability.contexts.glue context
    (capability.replacements.replacement input.seed.piece candidate)

theorem sourceObject_current :
    sourceObject capability ctx input
      (capability.contexts.currentContext input.seed.piece) = ctx.G :=
  capability.contexts.reconstruct input.seed.piece

/-- Exact reference observation of the source piece in one context. -/
def sourceObservation
    (context : capability.contexts.Context
      (capability.interfaces.interface input.seed.piece)) : Core.ExactObservation :=
  capability.observable.observe (sourceObject capability ctx input context)

/-- Exact reference observation of one legal replacement in one context. -/
def replacementObservation
    (candidate : capability.replacements.Candidate input.seed.piece)
    (context : capability.contexts.Context
      (capability.interfaces.interface input.seed.piece)) : Core.ExactObservation :=
  capability.observable.observe
    (replacementObject capability ctx input candidate context)

/-- Context equivalence is exact equality of baseline/target truth pairs in
every context of the finite universe. -/
def ContextEquivalent
    (candidate : capability.replacements.Candidate input.seed.piece) : Prop :=
  ∀ context, sourceObservation capability ctx input context =
    replacementObservation capability ctx input candidate context

/-- A deletion branch retains the exact smaller counterexample found by
computation. -/
structure DeletionWitness : Prop where
  baseline : P.Baseline
    (capability.reductions.delete input.seed.piece).value
  avoids : ¬ Target (capability.reductions.delete input.seed.piece).value

/-- Failure of deletion to produce a smaller counterexample. -/
structure DeletionCriticalState : Prop where
  notCounterexample : ¬ (
    P.Baseline (capability.reductions.delete input.seed.piece).value ∧
    ¬ Target (capability.reductions.delete input.seed.piece).value)

/-- A legal replacement whose exact response agrees in every context. -/
structure ReplacementWitness where
  candidate : capability.replacements.Candidate input.seed.piece
  equivalent : ContextEquivalent capability ctx input candidate
  baseline : P.Baseline
    (capability.replacements.asSmaller input.seed.piece candidate).value
  avoids : ¬ Target
    (capability.replacements.asSmaller input.seed.piece candidate).value

/-- Canonical C2 evidence.  Its contradiction is derived generically from the
shared minimal-counterexample context. -/
inductive C2Certificate where
  | deletion (witness : DeletionWitness capability ctx input)
  | replacement (witness : ReplacementWitness capability ctx input)

namespace C2Certificate

theorem contradiction
    (certificate : C2Certificate capability ctx input) : False := by
  cases certificate with
  | deletion witness =>
      exact Core.SmallerObject.counterexample_impossible ctx
        (capability.reductions.delete input.seed.piece)
        witness.baseline witness.avoids
  | replacement witness =>
      exact Core.SmallerObject.counterexample_impossible ctx
        (capability.replacements.asSmaller input.seed.piece witness.candidate)
        witness.baseline witness.avoids

end C2Certificate

/-- One exact context distinguishing a candidate from the source piece. -/
structure ContextSeparator
    (candidate : capability.replacements.Candidate input.seed.piece) where
  context : capability.contexts.Context
    (capability.interfaces.interface input.seed.piece)
  differs : sourceObservation capability ctx input context ≠
    replacementObservation capability ctx input candidate context

namespace ContextSeparator

theorem notEquivalent
    {candidate : capability.replacements.Candidate input.seed.piece}
    (separator : ContextSeparator capability ctx input candidate) :
    ¬ ContextEquivalent capability ctx input candidate := by
  intro equivalent
  exact separator.differs (equivalent separator.context)

end ContextSeparator

/-- Complete exhaustive replacement table: every legal candidate has a named
first separating context. -/
structure ReplacementTable where
  separator : ∀ candidate : capability.replacements.Candidate input.seed.piece,
    ContextSeparator capability ctx input candidate

namespace ReplacementTable

theorem noEquivalent (table : ReplacementTable capability ctx input) :
    ∀ candidate : capability.replacements.Candidate input.seed.piece,
      ¬ ContextEquivalent capability ctx input candidate :=
  fun candidate => (table.separator candidate).notEquivalent

end ReplacementTable

/-- A deterministic separating residual.  The complete table is retained so
the residual certifies that no later candidate was silently ignored. -/
structure SeparatingContextResidual where
  deletionCritical : DeletionCriticalState capability ctx input
  candidate : capability.replacements.Candidate input.seed.piece
  separator : ContextSeparator capability ctx input candidate
  replacementTable : ReplacementTable capability ctx input

/-- Exhaustive criticality is emitted exactly when the legal replacement
universe is empty. -/
structure CriticalityResidual where
  deletionCritical : DeletionCriticalState capability ctx input
  replacementTable : ReplacementTable capability ctx input
  noCandidate : ∀ _candidate : capability.replacements.Candidate input.seed.piece, False

end StructuralExhaustion.CT2
