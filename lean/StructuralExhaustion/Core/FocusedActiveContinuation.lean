import StructuralExhaustion.Core.ResidualRefinement

namespace StructuralExhaustion.Core.ResidualRefinement.State

universe uInput uOccurrence uResidual uStage uTarget

/-!
# Successors of a focused active continuation

These carriers cover the common situation in which a proof diagram has
already focused one live leaf, appended one payload there, and must continue
or decide that same leaf again.  The framework retains the literal active
data and current payload; an application supplies only the next local
mathematical value or predicate.
-/

/-- The literal active data and current output of a focused continuation,
bundled inside Core so applications do not construct transport records. -/
structure FocusedBranchActiveData
    {Residual : Type uResidual}
    (Active : Residual → Type uInput)
    (Current : (residual : Residual) → Active residual → Type uTarget)
    (residual : Residual) : Type (max uInput uTarget) where
  data : Active residual
  output : Current residual data

/-- The sole live no leaf after a focused decision's yes constructor has
been closed.  Keeping the branch proof in Core makes the next application
node a plain local producer. -/
structure FocusedBranchDecisionYesClosedActive
    {Residual : Type uResidual}
    (Active : Residual → Type uInput)
    (no : (residual : Residual) → Active residual → Prop)
    (residual : Residual) : Type uInput where
  data : Active residual
  proof : no residual data

variable {Residual : Type uResidual}
variable {facts : List (Residual → Prop)}

/-- Replace the payload on the live leaf of a focused active continuation.
The preceding continuation remains in the accumulated ledger, and Core
transports the bypass constructor literally. -/
noncomputable def StageNode.mapFocusedBranchActiveContinuation
    {Bypass : Residual → Type uInput}
    {Active : Residual → Type uTarget}
    {Current : (residual : Residual) → Active residual → Type uStage}
    {Next : (residual : Residual) → Active residual → Type uOccurrence}
    [Proofs.Contains
      (Available (FocusedBranchActiveContinuation Bypass Active Current)) facts]
    (produce : ∀ residual data,
      Current residual data → Next residual data) :
    StageNode (facts := facts)
      (FocusedBranchActiveContinuation Bypass Active Next) :=
  StageNode.usingStage
    (Required := FocusedBranchActiveContinuation Bypass Active Current)
      fun state continuation =>
        match continuation with
        | .bypass data => .bypass data
        | .active data current =>
            .active data (produce state.residual data current)

/-- Append a second payload to the live leaf while retaining the literal
current payload inside a Core-owned active-data bundle.  This is the
data-bearing analogue of advancing a dependent decision continuation. -/
noncomputable def StageNode.continueFocusedBranchActiveAgain
    {Bypass : Residual → Type uInput}
    {Active : Residual → Type uTarget}
    {Current : (residual : Residual) → Active residual → Type uStage}
    {Next : (residual : Residual) →
      FocusedBranchActiveData Active Current residual → Type uOccurrence}
    [Proofs.Contains
      (Available (FocusedBranchActiveContinuation Bypass Active Current)) facts]
    (produce : ∀ residual data current,
      Next residual ⟨data, current⟩) :
    StageNode (facts := facts)
      (FocusedBranchActiveContinuation Bypass
        (FocusedBranchActiveData Active Current) Next) :=
  StageNode.usingStage
    (Required := FocusedBranchActiveContinuation Bypass Active Current)
      fun state continuation =>
        match continuation with
        | .bypass data => .bypass data
        | .active data current =>
            .active ⟨data, current⟩
              (produce state.residual data current)

/-- Exhaustively decide one predicate on the literal current leaf of a
focused active continuation.  Core owns the active-data bundle and both
decision constructors. -/
noncomputable def StageNode.decideFocusedBranchActiveContinuation
    {Bypass : Residual → Type uInput}
    {Active : Residual → Type uTarget}
    {Current : (residual : Residual) → Active residual → Type uStage}
    {yes no : (residual : Residual) →
      FocusedBranchActiveData Active Current residual → Prop}
    [Proofs.Contains
      (Available (FocusedBranchActiveContinuation Bypass Active Current)) facts]
    (decideYes : ∀ residual data current,
      Decidable (yes residual ⟨data, current⟩))
    (noOfNotYes : ∀ residual data current,
      ¬ yes residual ⟨data, current⟩ →
        no residual ⟨data, current⟩) :
    StageNode (facts := facts)
      (FocusedBranchDecision Bypass
        (FocusedBranchActiveData Active Current) yes no) :=
  StageNode.usingStage
    (Required := FocusedBranchActiveContinuation Bypass Active Current)
      fun state continuation =>
        match continuation with
        | .bypass data => .bypass data
        | .active data current =>
            match decideYes state.residual data current with
            | .isTrue proof => .yesBranch ⟨data, current⟩ proof
            | .isFalse absent =>
                .noBranch ⟨data, current⟩
                  (noOfNotYes state.residual data current absent)

/-- Continue the exact no leaf left after closing a focused decision's yes
constructor.  Core retains the bypass and branch proof and appends only the
next node's local payload. -/
noncomputable def StageNode.continueFocusedBranchDecisionYesClosed
    {Bypass : Residual → Type uInput}
    {Active : Residual → Type uTarget}
    {yes no : (residual : Residual) → Active residual → Prop}
    {Output : (residual : Residual) →
      FocusedBranchDecisionYesClosedActive Active no residual →
        Type uOccurrence}
    [Proofs.Contains
      (Available (FocusedBranchDecisionYesClosed
        Bypass Active yes no)) facts]
    (produce : ∀ residual data proof,
      Output residual ⟨data, proof⟩) :
    StageNode (facts := facts)
      (FocusedBranchActiveContinuation Bypass
        (FocusedBranchDecisionYesClosedActive Active no) Output) :=
  StageNode.usingStage
    (Required := FocusedBranchDecisionYesClosed Bypass Active yes no)
      fun state decision =>
        match decision with
        | .bypass data => .bypass data
        | .activeNo data proof =>
            .active ⟨data, proof⟩
              (produce state.residual data proof)

end StructuralExhaustion.Core.ResidualRefinement.State
