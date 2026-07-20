import StructuralExhaustion.CT1.ResidualRefinement

namespace StructuralExhaustion.Examples.CT1DependentCertificateFamily

open StructuralExhaustion

/-!
A small non-graph fixture for the predecessor-dependent certificate executor.
The predecessor Boolean determines the problem rank, public target, encoding,
and inherited input.  The framework retrieves that Boolean once and performs
the corresponding CT1 decision without casts or application routing.
-/

def Previous (_ : Unit) := Bool

def problem (previous : Bool) : Core.Problem where
  Ambient := Bool
  Baseline := fun _ => True
  rank := fun value => if value = previous then 0 else 1
  BranchState := fun _ => Unit

def publicTarget (previous value : Bool) : Prop := value = previous

def encoding (previous : Bool) :
    CT1.TargetCertificateEncoding (P := problem previous)
      (publicTarget previous) where
  Code := fun _ => Unit
  Accepts := fun value _ => value = previous
  encode := fun target => ⟨(), target⟩
  decode := fun accepts => accepts

def input (previous : Bool) : CT1.Input (problem previous) where
  context := {
    G := previous
    baseline := trivial
    state := ()
  }

def family : CT1.ResidualRefinement.DependentCertificateFamily Unit Previous where
  problem := fun _residual previous => problem previous
  PublicTarget := fun _residual previous => publicTarget previous
  encoding := fun _residual previous => encoding previous
  input := fun _residual previous => input previous

abbrev predecessorAvailable : Unit → Prop :=
  Core.ResidualRefinement.State.Available Previous

def predecessorState :
    Core.ResidualRefinement.State Unit [predecessorAvailable] :=
  (Core.ResidualRefinement.State.initial ()).add predecessorAvailable ⟨true⟩

noncomputable def decisionState :=
  (family.executeUsingStage).run predecessorState

noncomputable def decision : family.DecisionSuccessor () :=
  decisionState.requireStage

theorem decision_verified :
    match decision.output with
    | .c1 run => CT1.OutcomeClaim run.result.outcome
    | .avoiding run => CT1.OutcomeClaim run.result.outcome := by
  cases decision.output with
  | c1 run => exact run.result.verified
  | avoiding run => exact run.result.verified

noncomputable def continuationState :=
  (family.continuePublicTargetUsingStage).run decisionState

noncomputable def continuation : family.PublicTargetSuccessor () :=
  continuationState.requireStage

theorem continuation_verified :
    match continuation.output with
    | .c1 run _target => CT1.OutcomeClaim run.result.outcome
    | .avoiding run => CT1.OutcomeClaim run.result.outcome := by
  cases continuation.output with
  | c1 run _target => exact run.result.verified
  | avoiding run => exact run.result.verified

/-! ### Dependent avoiding continuation -/

/-- A second predecessor-indexed target that is false at the inherited input,
so the exact same family executor exercises its avoiding constructor. -/
def avoidingPublicTarget (previous value : Bool) : Prop := value ≠ previous

def avoidingEncoding (previous : Bool) :
    CT1.TargetCertificateEncoding (P := problem previous)
      (avoidingPublicTarget previous) where
  Code := fun _ => Unit
  Accepts := fun value _ => value ≠ previous
  encode := fun target => ⟨(), target⟩
  decode := fun accepts => accepts

def avoidingFamily :
    CT1.ResidualRefinement.DependentCertificateFamily Unit Previous where
  problem := fun _residual previous => problem previous
  PublicTarget := fun _residual previous => avoidingPublicTarget previous
  encoding := fun _residual previous => avoidingEncoding previous
  input := fun _residual previous => input previous

noncomputable def avoidingDecisionState :=
  (avoidingFamily.executeUsingStage).run predecessorState

/-- The fixture's only local avoiding-edge obligation: retain the framework's
zero-check certificate. -/
abbrev AvoidingPayload (_residual : Unit) (previous : Bool)
    (run : CT1.CertifiedAvoidingRun
      (avoidingFamily.encoding () previous).spec
      (avoidingFamily.input () previous)) : Type :=
  PLift (run.checks = 0)

def produceAvoidingPayload (_residual : Unit) (previous : Bool)
    (run : CT1.CertifiedAvoidingRun
      (avoidingFamily.encoding () previous).spec
      (avoidingFamily.input () previous)) :
    AvoidingPayload () previous run :=
  ⟨run.checks_eq⟩

noncomputable def avoidingContinuationState :=
  (avoidingFamily.continueAvoidingUsingStage produceAvoidingPayload).run
    avoidingDecisionState

noncomputable def avoidingContinuation :
    CT1.ResidualRefinement.DependentAvoidingContinuation
      avoidingFamily AvoidingPayload () :=
  avoidingContinuationState.requireStage

theorem avoiding_continuation_verified :
    match avoidingContinuation with
    | .c1 _previous run => CT1.OutcomeClaim run.result.outcome
    | .avoiding _previous run output =>
        CT1.OutcomeClaim run.result.outcome ∧ output.down = run.checks_eq := by
  cases avoidingContinuation with
  | c1 _previous run => exact run.result.verified
  | avoiding _previous run output =>
      exact ⟨run.result.verified, Subsingleton.elim _ _⟩

/-! ### Close the impossible public-target edge and retain avoidance -/

/-- The target `value ≠ previous` is impossible at this family's inherited
input `value = previous`.  This is the only mathematical fact supplied by the
fixture; CT1 owns certificate interpretation, branch closure, and retention
of the exact avoiding run. -/
theorem avoidingFamily_avoidsAtInput (_residual : Unit) (previous : Bool) :
    ¬ avoidingFamily.PublicTarget () previous
        (avoidingFamily.input () previous).context.G := by
  simp [avoidingFamily, avoidingPublicTarget, input]

noncomputable def avoidingClosedState :=
  (avoidingFamily.closePublicTargetContinueAvoidingUsingStage
    avoidingFamily_avoidsAtInput).run avoidingDecisionState

noncomputable def avoidingClosed : avoidingFamily.AvoidingSuccessor () :=
  avoidingClosedState.requireStage

theorem avoiding_closed_retains_exact_run :
    avoidingClosed.output.checks = 0 :=
  avoidingClosed.output.checks_eq

/-! ### Generic terminal closure of a dependent yes edge -/

abbrev ImpossibleYes (_residual : Unit) (previous : Bool) : Prop :=
  previous ≠ previous

abbrev ReflexiveNo (_residual : Unit) (previous : Bool) : Prop :=
  previous = previous

abbrev ClosingDecision :=
  Core.ResidualRefinement.State.DependentDecision Previous ImpossibleYes ReflexiveNo

def closingDecisionState :
    Core.ResidualRefinement.State Unit
      [Core.ResidualRefinement.State.Available ClosingDecision] :=
    (Core.ResidualRefinement.State.initial ()).add
    (Core.ResidualRefinement.State.Available ClosingDecision)
    ⟨Core.ResidualRefinement.State.DependentDecision.noBranch true rfl⟩

noncomputable def closedDecisionState :
    Core.ResidualRefinement.State Unit
      [Core.ResidualRefinement.State.Available
        (Core.ResidualRefinement.State.DependentDecisionYesClosed
          Previous ImpossibleYes ReflexiveNo),
       Core.ResidualRefinement.State.Available ClosingDecision] := by
  let node : Core.ResidualRefinement.State.StageNode
      (facts := [Core.ResidualRefinement.State.Available ClosingDecision])
      (Core.ResidualRefinement.State.DependentDecisionYesClosed
        Previous ImpossibleYes ReflexiveNo) :=
    Core.ResidualRefinement.State.StageNode.closeDependentDecisionYes
      (fun _residual _previous impossible => impossible rfl)
  exact node.run closingDecisionState

noncomputable def closedDecision :
    Core.ResidualRefinement.State.DependentDecisionYesClosed
      Previous ImpossibleYes ReflexiveNo () :=
  Core.ResidualRefinement.State.requireStage closedDecisionState

theorem closed_decision_retains_no :
    ReflexiveNo () closedDecision.previous :=
  closedDecision.proof

#print axioms decision_verified
#print axioms continuation_verified
#print axioms avoiding_continuation_verified
#print axioms avoiding_closed_retains_exact_run
#print axioms closed_decision_retains_no

end StructuralExhaustion.Examples.CT1DependentCertificateFamily
