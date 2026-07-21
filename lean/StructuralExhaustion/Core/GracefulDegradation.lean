import StructuralExhaustion.Core.ResidualRefinement

namespace StructuralExhaustion.Core.ResidualRefinement.State

universe uInput uOccurrence uResidual uStage uTarget

/-!
# Guarded graceful degradation

These carriers implement a common structural-exhaustion pattern.  One live
leaf is expected to close after a locally decidable guard.  When the guard is
false, that exact failure remains a typed residual; an already existing
alternate leaf remains independently live.  The alternate may receive its
own payload before both leaves execute one common downstream producer.

The common producer sees only the shared active predecessor.  Its type makes
it impossible to consume either the failed guard or the alternate-branch
proof, while both remain retained in the resulting framework carrier.
-/

/-- Exact data on the branch where an intended guarded closure is unavailable. -/
structure GuardFailureData
    {Residual : Type uResidual}
    (Active : Residual → Type uInput)
    (outerNo : (residual : Residual) → Active residual → Prop)
    (innerYes : (residual : Residual) →
      (data : Active residual) → outerNo residual data → Prop)
    (guard : (residual : Residual) → (data : Active residual) →
      (outerProof : outerNo residual data) →
      innerYes residual data outerProof → Prop)
    (residual : Residual) : Type uInput where
  data : Active residual
  outerProof : outerNo residual data
  innerProof : innerYes residual data outerProof
  guardFailure : ¬ guard residual data outerProof innerProof

/-- The exhaustive result after terminalizing the outer yes leaf and trying
the guarded closure on the inner yes leaf. -/
inductive GuardedDegradation
    {Residual : Type uResidual}
    (Bypass : Residual → Type uInput)
    (Active : Residual → Type uTarget)
    (outerYes outerNo : (residual : Residual) → Active residual → Prop)
    (OuterYesOutput : (residual : Residual) → (data : Active residual) →
      outerYes residual data → Type uStage)
    (innerYes innerNo : (residual : Residual) →
      (data : Active residual) → outerNo residual data → Prop)
    (Terminal : (residual : Residual) → (data : Active residual) →
      (proof : outerYes residual data) →
      OuterYesOutput residual data proof → Type uOccurrence)
    (guard : (residual : Residual) → (data : Active residual) →
      (outerProof : outerNo residual data) →
      innerYes residual data outerProof → Prop)
    (residual : Residual) :
    Type (max uInput uTarget uStage uOccurrence) where
  | bypass
      (data : FocusedBranchYesTerminalBypass Bypass Active outerYes
        OuterYesOutput Terminal residual)
  | degraded
      (data : GuardFailureData Active outerNo innerYes guard residual)
  | alternate
      (data : FocusedBranchNestedNoActive Active outerNo innerNo residual)

/-- Continue only the original alternate leaf while retaining the exact guard
failure and all terminal bypass data. -/
inductive GuardedDegradationAlternateContinuation
    {Residual : Type uResidual}
    (Bypass : Residual → Type uInput)
    (Active : Residual → Type uTarget)
    (outerYes outerNo : (residual : Residual) → Active residual → Prop)
    (OuterYesOutput : (residual : Residual) → (data : Active residual) →
      outerYes residual data → Type uStage)
    (innerYes innerNo : (residual : Residual) →
      (data : Active residual) → outerNo residual data → Prop)
    (Terminal : (residual : Residual) → (data : Active residual) →
      (proof : outerYes residual data) →
      OuterYesOutput residual data proof → Type uOccurrence)
    (guard : (residual : Residual) → (data : Active residual) →
      (outerProof : outerNo residual data) →
      innerYes residual data outerProof → Prop)
    (AlternateOutput : (residual : Residual) →
      FocusedBranchNestedNoActive Active outerNo innerNo residual →
        Type uOccurrence)
    (residual : Residual) :
    Type (max uInput uTarget uStage uOccurrence) where
  | bypass
      (data : FocusedBranchYesTerminalBypass Bypass Active outerYes
        OuterYesOutput Terminal residual)
  | degraded
      (data : GuardFailureData Active outerNo innerYes guard residual)
  | alternate
      (data : FocusedBranchNestedNoActive Active outerNo innerNo residual)
      (output : AlternateOutput residual data)

/-- Both live reasons after their common downstream mathematics has been
proved.  The reasons remain typed provenance, but `Next` depends only on the
shared active predecessor. -/
inductive GuardedDegradationMerged
    {Residual : Type uResidual}
    (Bypass : Residual → Type uInput)
    (Active : Residual → Type uTarget)
    (outerYes outerNo : (residual : Residual) → Active residual → Prop)
    (OuterYesOutput : (residual : Residual) → (data : Active residual) →
      outerYes residual data → Type uStage)
    (innerYes innerNo : (residual : Residual) →
      (data : Active residual) → outerNo residual data → Prop)
    (Terminal : (residual : Residual) → (data : Active residual) →
      (proof : outerYes residual data) →
      OuterYesOutput residual data proof → Type uOccurrence)
    (guard : (residual : Residual) → (data : Active residual) →
      (outerProof : outerNo residual data) →
      innerYes residual data outerProof → Prop)
    (AlternateOutput : (residual : Residual) →
      FocusedBranchNestedNoActive Active outerNo innerNo residual →
        Type uOccurrence)
    (Next : (residual : Residual) → Active residual → Type uOccurrence)
    (residual : Residual) :
    Type (max uInput uTarget uStage uOccurrence) where
  | bypass
      (data : FocusedBranchYesTerminalBypass Bypass Active outerYes
        OuterYesOutput Terminal residual)
  | degraded
      (data : GuardFailureData Active outerNo innerYes guard residual)
      (output : Next residual data.data)
  | alternate
      (data : FocusedBranchNestedNoActive Active outerNo innerNo residual)
      (alternateOutput : AlternateOutput residual data)
      (output : Next residual data.data)

variable {Residual : Type uResidual}
variable {facts : List (Residual → Prop)}

/-- Terminalize the outer yes leaf, close the inner yes leaf when `guard`
holds, and otherwise retain either the exact guard failure or the original
inner-no residual. -/
noncomputable def StageNode.terminalizeGuardOrDegrade
    {Bypass : Residual → Type uInput}
    {Active : Residual → Type uTarget}
    {outerYes outerNo : (residual : Residual) → Active residual → Prop}
    {OuterYesOutput : (residual : Residual) → (data : Active residual) →
      outerYes residual data → Type uStage}
    {innerYes innerNo : (residual : Residual) →
      (data : Active residual) → outerNo residual data → Prop}
    {Terminal : (residual : Residual) → (data : Active residual) →
      (proof : outerYes residual data) →
      OuterYesOutput residual data proof → Type uOccurrence}
    {guard : (residual : Residual) → (data : Active residual) →
      (outerProof : outerNo residual data) →
      innerYes residual data outerProof → Prop}
    [Proofs.Contains (Available
      (FocusedBranchYesContinuationNoDecision Bypass Active outerYes outerNo
        OuterYesOutput innerYes innerNo)) facts]
    (terminal : ∀ residual data proof output,
      Terminal residual data proof output)
    (decideGuard : ∀ residual data outerProof innerProof,
      Decidable (guard residual data outerProof innerProof))
    (close : ∀ residual data outerProof innerProof,
      guard residual data outerProof innerProof → False) :
    StageNode (facts := facts)
      (GuardedDegradation Bypass Active outerYes outerNo OuterYesOutput
        innerYes innerNo Terminal guard) :=
  StageNode.usingStage
    (Required := FocusedBranchYesContinuationNoDecision Bypass Active
      outerYes outerNo OuterYesOutput innerYes innerNo)
    fun state decision =>
      match decision with
      | .bypass data => .bypass (.bypass data)
      | .outerYesBranch data proof output =>
          .bypass (.terminal data proof output
            (terminal state.residual data proof output))
      | .innerYesBranch data outerProof innerProof =>
          match decideGuard state.residual data outerProof innerProof with
          | .isTrue proof =>
              (close state.residual data outerProof innerProof proof).elim
          | .isFalse absent =>
              .degraded ⟨data, outerProof, innerProof, absent⟩
      | .innerNoBranch data outerProof innerProof =>
          .alternate ⟨data, outerProof, innerProof⟩

/-- Append one payload only on the original alternate leaf. -/
noncomputable def StageNode.continueGuardedDegradationAlternate
    {Bypass : Residual → Type uInput}
    {Active : Residual → Type uTarget}
    {outerYes outerNo : (residual : Residual) → Active residual → Prop}
    {OuterYesOutput : (residual : Residual) → (data : Active residual) →
      outerYes residual data → Type uStage}
    {innerYes innerNo : (residual : Residual) →
      (data : Active residual) → outerNo residual data → Prop}
    {Terminal : (residual : Residual) → (data : Active residual) →
      (proof : outerYes residual data) →
      OuterYesOutput residual data proof → Type uOccurrence}
    {guard : (residual : Residual) → (data : Active residual) →
      (outerProof : outerNo residual data) →
      innerYes residual data outerProof → Prop}
    {AlternateOutput : (residual : Residual) →
      FocusedBranchNestedNoActive Active outerNo innerNo residual →
        Type uOccurrence}
    [Proofs.Contains (Available
      (GuardedDegradation Bypass Active outerYes outerNo OuterYesOutput
        innerYes innerNo Terminal guard)) facts]
    (produce : ∀ residual data, AlternateOutput residual data) :
    StageNode (facts := facts)
      (GuardedDegradationAlternateContinuation Bypass Active outerYes outerNo
        OuterYesOutput innerYes innerNo Terminal guard AlternateOutput) :=
  StageNode.usingStage
    (Required := GuardedDegradation Bypass Active outerYes outerNo
      OuterYesOutput innerYes innerNo Terminal guard)
    fun state result =>
      match result with
      | .bypass data => .bypass data
      | .degraded data => .degraded data
      | .alternate data =>
          .alternate data (produce state.residual data)

/-- Execute one common downstream producer on both live leaves.  The producer
is parametrically unable to inspect their distinct reasons. -/
noncomputable def StageNode.mergeGuardedDegradation
    {Bypass : Residual → Type uInput}
    {Active : Residual → Type uTarget}
    {outerYes outerNo : (residual : Residual) → Active residual → Prop}
    {OuterYesOutput : (residual : Residual) → (data : Active residual) →
      outerYes residual data → Type uStage}
    {innerYes innerNo : (residual : Residual) →
      (data : Active residual) → outerNo residual data → Prop}
    {Terminal : (residual : Residual) → (data : Active residual) →
      (proof : outerYes residual data) →
      OuterYesOutput residual data proof → Type uOccurrence}
    {guard : (residual : Residual) → (data : Active residual) →
      (outerProof : outerNo residual data) →
      innerYes residual data outerProof → Prop}
    {AlternateOutput : (residual : Residual) →
      FocusedBranchNestedNoActive Active outerNo innerNo residual →
        Type uOccurrence}
    {Next : (residual : Residual) → Active residual → Type uOccurrence}
    [Proofs.Contains (Available
      (GuardedDegradationAlternateContinuation Bypass Active outerYes outerNo
        OuterYesOutput innerYes innerNo Terminal guard AlternateOutput)) facts]
    (produce : ∀ residual data, Next residual data) :
    StageNode (facts := facts)
      (GuardedDegradationMerged Bypass Active outerYes outerNo OuterYesOutput
        innerYes innerNo Terminal guard AlternateOutput Next) :=
  StageNode.usingStage
    (Required := GuardedDegradationAlternateContinuation Bypass Active
      outerYes outerNo OuterYesOutput innerYes innerNo Terminal guard
      AlternateOutput)
    fun state result =>
      match result with
      | .bypass data => .bypass data
      | .degraded data =>
          .degraded data (produce state.residual data.data)
      | .alternate data alternateOutput =>
          .alternate data alternateOutput (produce state.residual data.data)

end StructuralExhaustion.Core.ResidualRefinement.State
