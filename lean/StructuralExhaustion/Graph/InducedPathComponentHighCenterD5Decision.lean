import StructuralExhaustion.Graph.InducedPathComponentD5Availability
import StructuralExhaustion.Graph.InducedPathComponentHighCenterSplit

namespace StructuralExhaustion.Graph.InducedPathComponentHighCenterD5Decision

open StructuralExhaustion

universe u

/-! The current component branch first performs the graph-derived high-center
split.  A high center supplies a D6 center input and its local incidence
subfamily, without claiming D6 closure.  The no-high branch retains ambient
cubicity and records exactly the two manuscript facts still needed before
Type A D5 ownership can be assembled. -/

variable {input : PackedMinimumDegreeCycle.StaticInput}
variable {ctx : Core.MinimalCounterexampleContext input.problem input.Target}
variable {setup : SurplusPortActivation.Setup input ctx}
variable (stage : SurplusPortActivation.VerifiedActivatedStage input ctx setup)
variable (componentInput : InducedPathComponentBoundarySchedule.Input ctx.G.object)
variable (LengthOK : Nat → Prop)
variable (lengthOKDecidable : DecidablePred LengthOK)

inductive MissingTypeAFact
  | p13FreeOnSupport
  | internalCoreFree
  deriving DecidableEq, Repr

def missingTypeAFacts : List MissingTypeAFact :=
  [.p13FreeOnSupport, .internalCoreFree]

theorem missingTypeAFacts_nodup : missingTypeAFacts.Nodup := by decide

structure NoHighResidual
    {source : Nonempty (InducedPathComponentD4Evaluator.Marker componentInput)}
    {ledger : InducedPathComponentD4Evaluator.Previous.Ledger source}
    {focused : InducedPathComponentD4Evaluator.Previous.Cursor ledger}
    {request : InducedPathComponentD4Evaluator.Previous.Request focused}
    {evaluatorPending : InducedPathComponentD4EvaluatorResidual.Residual request}
    {build : InducedPathComponentD4EvaluatorConstructionResidual.Residual
      evaluatorPending}
    {d4 : InducedPathComponentD4Evaluator.Evaluation componentInput LengthOK
      lengthOKDecidable build}
    (previous : InducedPathComponentD4D7Evaluation.Evaluation stage componentInput
      LengthOK lengthOKDecidable d4)
    (minimumDegreeThree : 3 ≤ ctx.G.object.minDegree) where
  predecessor : InducedPathComponentD4D7Evaluation.Evaluation stage componentInput
    LengthOK lengthOKDecidable d4
  predecessorExact : predecessor = previous
  split : InducedPathComponentHighCenterSplit.NoHigh ctx.G.object componentInput
    minimumDegreeThree
  missing : List MissingTypeAFact
  missingExact : missing = missingTypeAFacts
  missingNodup : missing.Nodup
  d5Pending : Bool
  d5PendingExact : d5Pending = true
  d6AbsentOnActiveSupport :
    InducedPathComponentHighCenterSplit.activeHighCenters ctx.G.object
      componentInput = ∅

inductive Result
    {source : Nonempty (InducedPathComponentD4Evaluator.Marker componentInput)}
    {ledger : InducedPathComponentD4Evaluator.Previous.Ledger source}
    {focused : InducedPathComponentD4Evaluator.Previous.Cursor ledger}
    {request : InducedPathComponentD4Evaluator.Previous.Request focused}
    {evaluatorPending : InducedPathComponentD4EvaluatorResidual.Residual request}
    {build : InducedPathComponentD4EvaluatorConstructionResidual.Residual
      evaluatorPending}
    {d4 : InducedPathComponentD4Evaluator.Evaluation componentInput LengthOK
      lengthOKDecidable build}
    (previous : InducedPathComponentD4D7Evaluation.Evaluation stage componentInput
      LengthOK lengthOKDecidable d4)
    (minimumDegreeThree : 3 ≤ ctx.G.object.minDegree) where
  | high
      (predecessor : InducedPathComponentD4D7Evaluation.Evaluation stage
        componentInput LengthOK lengthOKDecidable d4)
      (predecessorExact : predecessor = previous)
      (output : InducedPathComponentHighCenterSplit.High ctx.G.object componentInput)
  | noHigh (residual : NoHighResidual stage componentInput LengthOK
      lengthOKDecidable previous minimumDegreeThree)

noncomputable def run
    {source : Nonempty (InducedPathComponentD4Evaluator.Marker componentInput)}
    {ledger : InducedPathComponentD4Evaluator.Previous.Ledger source}
    {focused : InducedPathComponentD4Evaluator.Previous.Cursor ledger}
    {request : InducedPathComponentD4Evaluator.Previous.Request focused}
    {evaluatorPending : InducedPathComponentD4EvaluatorResidual.Residual request}
    {build : InducedPathComponentD4EvaluatorConstructionResidual.Residual
      evaluatorPending}
    {d4 : InducedPathComponentD4Evaluator.Evaluation componentInput LengthOK
      lengthOKDecidable build}
    (previous : InducedPathComponentD4D7Evaluation.Evaluation stage componentInput
      LengthOK lengthOKDecidable d4)
    (minimumDegreeThree : 3 ≤ ctx.G.object.minDegree) :
    Result stage componentInput LengthOK lengthOKDecidable previous
      minimumDegreeThree := by
  cases InducedPathComponentHighCenterSplit.run ctx.G.object componentInput
      minimumDegreeThree with
  | high output => exact .high previous rfl output
  | noHigh output => exact .noHigh {
      predecessor := previous
      predecessorExact := rfl
      split := output
      missing := missingTypeAFacts
      missingExact := rfl
      missingNodup := missingTypeAFacts_nodup
      d5Pending := true
      d5PendingExact := rfl
      d6AbsentOnActiveSupport := output.highCentersEmpty
    }

theorem run_exhaustive
    {source : Nonempty (InducedPathComponentD4Evaluator.Marker componentInput)}
    {ledger : InducedPathComponentD4Evaluator.Previous.Ledger source}
    {focused : InducedPathComponentD4Evaluator.Previous.Cursor ledger}
    {request : InducedPathComponentD4Evaluator.Previous.Request focused}
    {evaluatorPending : InducedPathComponentD4EvaluatorResidual.Residual request}
    {build : InducedPathComponentD4EvaluatorConstructionResidual.Residual
      evaluatorPending}
    {d4 : InducedPathComponentD4Evaluator.Evaluation componentInput LengthOK
      lengthOKDecidable build}
    (previous : InducedPathComponentD4D7Evaluation.Evaluation stage componentInput
      LengthOK lengthOKDecidable d4)
    (minimumDegreeThree : 3 ≤ ctx.G.object.minDegree) :
    (∃ predecessor exact high, run stage componentInput LengthOK
      lengthOKDecidable previous minimumDegreeThree =
        .high predecessor exact high) ∨
    (∃ residual, run stage componentInput LengthOK lengthOKDecidable previous
      minimumDegreeThree = .noHigh residual) := by
  cases equation : run stage componentInput LengthOK lengthOKDecidable previous
      minimumDegreeThree with
  | high predecessor exact output => exact Or.inl ⟨predecessor, exact, output, rfl⟩
  | noHigh residual => exact Or.inr ⟨residual, rfl⟩

end StructuralExhaustion.Graph.InducedPathComponentHighCenterD5Decision
