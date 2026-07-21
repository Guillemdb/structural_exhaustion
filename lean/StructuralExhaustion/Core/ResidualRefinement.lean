import StructuralExhaustion.Core.FiniteResidualLedger
import StructuralExhaustion.Core.ExactHandoff
import StructuralExhaustion.Core.WorkBudget

namespace StructuralExhaustion.Core.ResidualRefinement

universe uOccurrence uNext uResidual uTarget uInput uStage

/-!
# Accumulating residual refinements

A branch keeps one stable residual carrier.  Every node proves only its new
property; the framework retains the residual and all earlier proofs.
-/

/-- The dependent proof bundle for an ordered list of residual properties. -/
inductive Proofs {Residual : Type uResidual} (residual : Residual) :
    List (Residual → Prop) → Type uResidual where
  | nil : Proofs residual []
  | cons {property properties} :
      property residual → Proofs residual properties →
        Proofs residual (property :: properties)

namespace Proofs

variable {Residual : Type uResidual} {residual : Residual}
variable {property : Residual → Prop} {properties : List (Residual → Prop)}

def head (proofs : Proofs residual (property :: properties)) :
    property residual := by
  cases proofs with
  | cons proof _ => exact proof

def tail (proofs : Proofs residual (property :: properties)) :
    Proofs residual properties := by
  cases proofs with
  | cons _ earlier => exact earlier

/-- A typed position of one property in an accumulated proof bundle. -/
inductive Member (wanted : Residual → Prop) :
    List (Residual → Prop) → Type uResidual where
  | here {rest} : Member wanted (wanted :: rest)
  | there {other rest} : Member wanted rest →
      Member wanted (other :: rest)

/-- Type-directed access to an accumulated property.  The newest occurrence
of a repeated property wins, matching the stack discipline of `State.add`.
Explicit `Member` values remain available when a consumer intentionally needs
an older duplicate. -/
class Contains (wanted : Residual → Prop)
    (facts : List (Residual → Prop)) where
  member : Member wanted facts

instance (priority := high) containsHere
    {wanted : Residual → Prop} {rest : List (Residual → Prop)} :
    Contains wanted (wanted :: rest) where
  member := .here

instance (priority := low) containsThere
    {wanted other : Residual → Prop}
    {rest : List (Residual → Prop)}
    [Contains wanted rest] : Contains wanted (other :: rest) where
  member := .there (Contains.member (wanted := wanted) (facts := rest))

def get {wanted : Residual → Prop} {facts : List (Residual → Prop)}
    (proofs : Proofs residual facts) (member : Member wanted facts) :
    wanted residual := by
  induction member with
  | here => exact proofs.head
  | there member ih => exact ih proofs.tail

end Proofs

/-- One current branch residual with every property established so far. -/
structure State (Residual : Type uResidual)
    (facts : List (Residual → Prop)) where
  residual : Residual
  proofs : Proofs residual facts

namespace State

variable {Residual : Type uResidual}
variable {facts : List (Residual → Prop)}

/-- A proof-level certificate stage available at a stable residual. -/
def Available (Stage : Residual → Sort uTarget)
    (residual : Residual) : Prop :=
  Nonempty (Stage residual)

def initial (residual : Residual) : State Residual [] where
  residual := residual
  proofs := .nil

/-- Add exactly one new proved property while retaining all earlier facts. -/
def add (state : State Residual facts) (property : Residual → Prop)
    (proof : property state.residual) :
    State Residual (property :: facts) where
  residual := state.residual
  proofs := .cons proof state.proofs

@[simp] theorem add_residual (state : State Residual facts)
    (property : Residual → Prop) (proof : property state.residual) :
    (state.add property proof).residual = state.residual :=
  rfl

def latest {property : Residual → Prop}
    (state : State Residual (property :: facts)) :
    property state.residual :=
  state.proofs.head

def earlier {property : Residual → Prop}
    (state : State Residual (property :: facts)) : State Residual facts where
  residual := state.residual
  proofs := state.proofs.tail

def get {property : Residual → Prop}
    (state : State Residual facts)
    (member : Proofs.Member property facts) : property state.residual :=
  state.proofs.get member

/-- Retrieve an accumulated fact by its predicate type.  Adding unrelated
properties to a refinement chain no longer changes consumer code. -/
def require {property : Residual → Prop}
    (state : State Residual facts)
    [Proofs.Contains property facts] : property state.residual :=
  state.get (Proofs.Contains.member (wanted := property) (facts := facts))

/-- The complete contract of one ordinary proof node.  Application code
supplies only `prove`; state extension is framework-owned. -/
structure Node (property : Residual → Prop) where
  prove : (state : State Residual facts) → property state.residual

/-- A data-bearing proof stage.  The framework stores availability as one
accumulated fact while the application supplies only the stage producer. -/
structure StageNode (Stage : Residual → Sort uTarget) where
  produce : (state : State Residual facts) → Stage state.residual

/-- A reusable theorem projection from a proof-carrying stage to one of its
mathematical consequences. The stage remains the sole ledger entry; later
consumers request registered consequences without copying predecessor data. -/
class StageEntails (Stage : Residual → Sort uTarget)
    (property : Residual → Prop) where
  prove : ∀ {residual}, Stage residual → property residual

/-- One literal accumulated stage together with a successor whose type may
depend on that exact retrieved value.  This is the framework-owned carrier
for a diagram edge whose target payload is predecessor-indexed but whose
predecessor has no separately named canonical value at the stable residual. -/
structure DependentSuccessor
    (Previous : Residual → Sort uInput)
    (Next : (residual : Residual) → Previous residual → Sort uTarget)
    (residual : Residual) where
  previous : Previous residual
  output : Next residual previous

namespace DependentSuccessor

/-- Framework-owned retrieval of the inherited predecessor payload from a
dependent successor.  Applications use this accessor instead of defining
node-specific projections for accumulated data. -/
abbrev inherited {Previous : Residual → Sort uInput}
    {Next : (residual : Residual) → Previous residual → Sort uTarget}
    {residual : Residual}
    (stage : DependentSuccessor Previous Next residual) :
    Previous residual :=
  stage.previous

/-- Framework-owned retrieval of the new local payload from a dependent
successor. -/
abbrev latest {Previous : Residual → Sort uInput}
    {Next : (residual : Residual) → Previous residual → Sort uTarget}
    {residual : Residual}
    (stage : DependentSuccessor Previous Next residual) :
    Next residual stage.previous :=
  stage.output

end DependentSuccessor

/-- An exhaustive decision about one literal data-bearing predecessor
retrieved from the accumulated ledger.  Both constructors retain that exact
value; applications cannot decide a proposition about one stage and attach
the result to another. -/
inductive DependentDecision
    (Previous : Residual → Type uInput)
    (yes no : (residual : Residual) → Previous residual → Prop)
    (residual : Residual) : Type uInput where
  | yesBranch (previous : Previous residual) (proof : yes residual previous) :
      DependentDecision Previous yes no residual
  | noBranch (previous : Previous residual) (proof : no residual previous) :
      DependentDecision Previous yes no residual

/-- A decision whose predecessor is already fixed by the surrounding
dependent stage. Unlike `DependentDecision`, this type stores no second copy
of that value, so a nested decision cannot silently switch predecessors. -/
inductive DependentDecisionAt
    {Previous : Residual → Type uInput}
    (yes no : (residual : Residual) → Previous residual → Prop)
    (residual : Residual) (previous : Previous residual) : Type where
  | yesBranch (proof : yes residual previous) :
      DependentDecisionAt yes no residual previous
  | noBranch (proof : no residual previous) :
      DependentDecisionAt yes no residual previous

/-- Result of closing the yes constructor of a dependent decision by
contradiction.  Only the literal no predecessor and its proof survive; the
framework never asks an application to fabricate an output on the closed
branch. -/
structure DependentDecisionYesClosed
    (Previous : Residual → Type uInput)
    (yes no : (residual : Residual) → Previous residual → Prop)
    (residual : Residual) where
  previous : Previous residual
  proof : no residual previous

namespace DependentDecisionAt

/-- Execute a decision at one literal predecessor. -/
noncomputable def decide
    {Previous : Residual → Type uInput}
    {yes no : (residual : Residual) → Previous residual → Prop}
    {residual : Residual} {previous : Previous residual}
    (yesDecidable : Decidable (yes residual previous))
    (no_of_not_yes : ¬yes residual previous → no residual previous) :
    DependentDecisionAt yes no residual previous :=
  match yesDecidable with
  | .isTrue proof => .yesBranch proof
  | .isFalse absent => .noBranch (no_of_not_yes absent)

end DependentDecisionAt

/-- Framework-owned continuation of only the yes edge of a dependent stage
decision.  The no edge retains the same predecessor and proof unchanged. -/
inductive DependentDecisionYesContinuation
    (Previous : Residual → Type uInput)
    (yes no : (residual : Residual) → Previous residual → Prop)
    (Next : (residual : Residual) → (previous : Previous residual) →
      yes residual previous → Type uTarget)
    (residual : Residual) : Type (max uInput uTarget) where
  | yesBranch (previous : Previous residual) (proof : yes residual previous)
      (output : Next residual previous proof) :
      DependentDecisionYesContinuation Previous yes no Next residual
  | noBranch (previous : Previous residual) (proof : no residual previous) :
      DependentDecisionYesContinuation Previous yes no Next residual

/-- Framework-owned continuation of only the no constructor of a dependent
decision.  The yes constructor is transported literally, while the no
constructor gains exactly one new mathematical payload.  This is the mirror
of `DependentDecisionYesContinuation`; it prevents applications whose next
paper node lies on the negative edge from inventing a dummy positive-edge
handoff. -/
inductive DependentDecisionNoContinuation
    (Previous : Residual → Type uInput)
    (yes no : (residual : Residual) → Previous residual → Prop)
    (Next : (residual : Residual) → (previous : Previous residual) →
      no residual previous → Type uTarget)
    (residual : Residual) : Type (max uInput uTarget) where
  | yesBranch (previous : Previous residual) (proof : yes residual previous) :
      DependentDecisionNoContinuation Previous yes no Next residual
  | noBranch (previous : Previous residual) (proof : no residual previous)
      (output : Next residual previous proof) :
      DependentDecisionNoContinuation Previous yes no Next residual

/-- A further successor on the yes edge of an already continued dependent
decision. The exact predecessor, its branch proof, and the current yes output
are retained by the framework; the no edge is passed through unchanged. -/
inductive DependentDecisionYesSuccessor
    (Previous : Residual → Type uInput)
    (yes no : (residual : Residual) → Previous residual → Prop)
    (Current : (residual : Residual) → (previous : Previous residual) →
      yes residual previous → Type uTarget)
    (Next : (residual : Residual) → (previous : Previous residual) →
      (proof : yes residual previous) → Current residual previous proof →
        Type uStage)
    (residual : Residual) : Type (max uInput uTarget uStage) where
  | yesBranch (previous : Previous residual) (proof : yes residual previous)
      (current : Current residual previous proof)
      (output : Next residual previous proof current) :
      DependentDecisionYesSuccessor Previous yes no Current Next residual
  | noBranch (previous : Previous residual) (proof : no residual previous) :
      DependentDecisionYesSuccessor Previous yes no Current Next residual

/-- Complete the no edge after the yes edge has already acquired an output.
The existing yes output is retained literally; only the no constructor gains
the newly produced mathematical payload. -/
inductive DependentDecisionNoAfterYes
    (Previous : Residual → Type uInput)
    (yes no : (residual : Residual) → Previous residual → Prop)
    (YesOutput : (residual : Residual) → (previous : Previous residual) →
      yes residual previous → Type uTarget)
    (NoOutput : (residual : Residual) → (previous : Previous residual) →
      no residual previous → Type uStage)
    (residual : Residual) : Type (max uInput uTarget uStage) where
  | yesBranch (previous : Previous residual) (proof : yes residual previous)
      (output : YesOutput residual previous proof) :
      DependentDecisionNoAfterYes Previous yes no YesOutput NoOutput residual
  | noBranch (previous : Previous residual) (proof : no residual previous)
      (output : NoOutput residual previous proof) :
      DependentDecisionNoAfterYes Previous yes no YesOutput NoOutput residual

/-- Continue the no leaf of a decision nested on the no edge of an earlier
decision. The outer yes output and inner yes leaf are retained unchanged. -/
inductive DependentNestedNoContinuation
    (Previous : Residual → Type uInput)
    (outerYes outerNo : (residual : Residual) → Previous residual → Prop)
    (OuterYesOutput : (residual : Residual) →
      (previous : Previous residual) → outerYes residual previous → Type uTarget)
    (innerYes innerNo : (residual : Residual) → Previous residual → Prop)
    (Next : (residual : Residual) → (previous : Previous residual) →
      outerNo residual previous → innerNo residual previous → Type uStage)
    (residual : Residual) : Type (max uInput uTarget uStage) where
  | outerYesBranch (previous : Previous residual)
      (proof : outerYes residual previous)
      (output : OuterYesOutput residual previous proof) :
      DependentNestedNoContinuation Previous outerYes outerNo OuterYesOutput
        innerYes innerNo Next residual

  | innerYesBranch (previous : Previous residual)
      (outerProof : outerNo residual previous)
      (innerProof : innerYes residual previous) :
      DependentNestedNoContinuation Previous outerYes outerNo OuterYesOutput
        innerYes innerNo Next residual
  | innerNoBranch (previous : Previous residual)
      (outerProof : outerNo residual previous)
      (innerProof : innerNo residual previous)
      (output : Next residual previous outerProof innerProof) :
      DependentNestedNoContinuation Previous outerYes outerNo OuterYesOutput
        innerYes innerNo Next residual

/-- A new exhaustive decision made only on the populated no leaf of an
earlier no-continuation.  The untouched outer yes leaf is transported
literally; the two inner constructors retain the exact outer-no payload. -/
inductive DependentDecisionOnNoContinuation
    (Previous : Residual → Type uInput)
    (outerYes outerNo : (residual : Residual) → Previous residual → Prop)
    (OuterNoOutput : (residual : Residual) →
      (previous : Previous residual) → outerNo residual previous → Type uTarget)
    (innerYes innerNo : (residual : Residual) →
      (previous : Previous residual) →
      (outerProof : outerNo residual previous) →
      OuterNoOutput residual previous outerProof → Prop)
    (residual : Residual) : Type (max uInput uTarget) where
  | outerYesBranch (previous : Previous residual)
      (proof : outerYes residual previous) :
      DependentDecisionOnNoContinuation Previous outerYes outerNo
        OuterNoOutput innerYes innerNo residual
  | innerYesBranch (previous : Previous residual)
      (outerProof : outerNo residual previous)
      (output : OuterNoOutput residual previous outerProof)
      (proof : innerYes residual previous outerProof output) :
      DependentDecisionOnNoContinuation Previous outerYes outerNo
        OuterNoOutput innerYes innerNo residual
  | innerNoBranch (previous : Previous residual)
      (outerProof : outerNo residual previous)
      (output : OuterNoOutput residual previous outerProof)
      (proof : innerNo residual previous outerProof output) :
      DependentDecisionOnNoContinuation Previous outerYes outerNo
        OuterNoOutput innerYes innerNo residual

/-- Continue only the inner-yes constructor of a decision made on an earlier
no continuation.  The unrelated outer-yes leaf and the complementary inner-no
leaf are transported literally. -/
inductive DependentDecisionOnNoYesContinuation
    (Previous : Residual → Type uInput)
    (outerYes outerNo : (residual : Residual) → Previous residual → Prop)
    (OuterNoOutput : (residual : Residual) →
      (previous : Previous residual) → outerNo residual previous → Type uTarget)
    (innerYes innerNo : (residual : Residual) →
      (previous : Previous residual) →
      (outerProof : outerNo residual previous) →
      OuterNoOutput residual previous outerProof → Prop)
    (YesOutput : (residual : Residual) →
      (previous : Previous residual) →
      (outerProof : outerNo residual previous) →
      (outerOutput : OuterNoOutput residual previous outerProof) →
      innerYes residual previous outerProof outerOutput → Type uStage)
    (residual : Residual) : Type (max uInput uTarget uStage) where
  | outerYesBranch (previous : Previous residual)
      (proof : outerYes residual previous) :
      DependentDecisionOnNoYesContinuation Previous outerYes outerNo
        OuterNoOutput innerYes innerNo YesOutput residual
  | innerYesBranch (previous : Previous residual)
      (outerProof : outerNo residual previous)
      (outerOutput : OuterNoOutput residual previous outerProof)
      (innerProof : innerYes residual previous outerProof outerOutput)
      (output : YesOutput residual previous outerProof outerOutput innerProof) :
      DependentDecisionOnNoYesContinuation Previous outerYes outerNo
        OuterNoOutput innerYes innerNo YesOutput residual
  | innerNoBranch (previous : Previous residual)
      (outerProof : outerNo residual previous)
      (outerOutput : OuterNoOutput residual previous outerProof)
      (innerProof : innerNo residual previous outerProof outerOutput) :
      DependentDecisionOnNoYesContinuation Previous outerYes outerNo
        OuterNoOutput innerYes innerNo YesOutput residual

/-- Complete the inner-no edge after the inner-yes edge has acquired its
successor payload.  This is the nested-decision analogue of
`DependentDecisionNoAfterYes`; all three literal constructors are retained. -/
inductive DependentDecisionOnNoNoAfterYes
    (Previous : Residual → Type uInput)
    (outerYes outerNo : (residual : Residual) → Previous residual → Prop)
    (OuterNoOutput : (residual : Residual) →
      (previous : Previous residual) → outerNo residual previous → Type uTarget)
    (innerYes innerNo : (residual : Residual) →
      (previous : Previous residual) →
      (outerProof : outerNo residual previous) →
      OuterNoOutput residual previous outerProof → Prop)
    (YesOutput : (residual : Residual) →
      (previous : Previous residual) →
      (outerProof : outerNo residual previous) →
      (outerOutput : OuterNoOutput residual previous outerProof) →
      innerYes residual previous outerProof outerOutput → Type uStage)
    (NoOutput : (residual : Residual) →
      (previous : Previous residual) →
      (outerProof : outerNo residual previous) →
      (outerOutput : OuterNoOutput residual previous outerProof) →
      innerNo residual previous outerProof outerOutput → Type uOccurrence)
    (residual : Residual) : Type
      (max uInput uTarget uStage uOccurrence) where
  | outerYesBranch (previous : Previous residual)
      (proof : outerYes residual previous) :
      DependentDecisionOnNoNoAfterYes Previous outerYes outerNo OuterNoOutput
        innerYes innerNo YesOutput NoOutput residual
  | innerYesBranch (previous : Previous residual)
      (outerProof : outerNo residual previous)
      (outerOutput : OuterNoOutput residual previous outerProof)
      (innerProof : innerYes residual previous outerProof outerOutput)
      (output : YesOutput residual previous outerProof outerOutput innerProof) :
      DependentDecisionOnNoNoAfterYes Previous outerYes outerNo OuterNoOutput
        innerYes innerNo YesOutput NoOutput residual
  | innerNoBranch (previous : Previous residual)
      (outerProof : outerNo residual previous)
      (outerOutput : OuterNoOutput residual previous outerProof)
      (innerProof : innerNo residual previous outerProof outerOutput)
      (output : NoOutput residual previous outerProof outerOutput innerProof) :
      DependentDecisionOnNoNoAfterYes Previous outerYes outerNo OuterNoOutput
        innerYes innerNo YesOutput NoOutput residual

/-- Result of closing the inner yes leaf of a decision made on an earlier
no-continuation.  The unrelated outer yes leaf and the complementary inner no
leaf survive literally. -/
inductive DependentDecisionOnNoYesClosed
    (Previous : Residual → Type uInput)
    (outerYes outerNo : (residual : Residual) → Previous residual → Prop)
    (OuterNoOutput : (residual : Residual) →
      (previous : Previous residual) → outerNo residual previous → Type uTarget)
    (innerYes innerNo : (residual : Residual) →
      (previous : Previous residual) →
      (outerProof : outerNo residual previous) →
      OuterNoOutput residual previous outerProof → Prop)
    (residual : Residual) : Type (max uInput uTarget) where
  | outerYesBranch (previous : Previous residual)
      (proof : outerYes residual previous) :
      DependentDecisionOnNoYesClosed Previous outerYes outerNo
        OuterNoOutput innerYes innerNo residual
  | innerNoBranch (previous : Previous residual)
      (outerProof : outerNo residual previous)
      (output : OuterNoOutput residual previous outerProof)
      (proof : innerNo residual previous outerProof output) :
      DependentDecisionOnNoYesClosed Previous outerYes outerNo
        OuterNoOutput innerYes innerNo residual

/-- A reusable active cursor after the inner-yes leaf of a nested decision has
been closed.  The untouched outer leaf remains a bypass, while the surviving
inner-no leaf carries exactly the latest mathematical output.  Repeated nodes
map the active payload through `mapDependentDecisionOnNoYesClosedActive`; the
complete earlier stages remain available in the accumulated ledger. -/
inductive DependentDecisionOnNoYesClosedActive
    (Previous : Residual → Type uInput)
    (outerYes outerNo : (residual : Residual) → Previous residual → Prop)
    (OuterNoOutput : (residual : Residual) →
      (previous : Previous residual) → outerNo residual previous → Type uTarget)
    (innerYes innerNo : (residual : Residual) →
      (previous : Previous residual) →
      (outerProof : outerNo residual previous) →
      OuterNoOutput residual previous outerProof → Prop)
    (Current : (residual : Residual) → (previous : Previous residual) →
      (outerProof : outerNo residual previous) →
      (outerOutput : OuterNoOutput residual previous outerProof) →
      innerNo residual previous outerProof outerOutput → Type uStage)
    (residual : Residual) : Type (max uInput uTarget uStage) where
  | outerYesBranch (previous : Previous residual)
      (proof : outerYes residual previous) :
      DependentDecisionOnNoYesClosedActive Previous outerYes outerNo
        OuterNoOutput innerYes innerNo Current residual
  | innerNoBranch (previous : Previous residual)
      (outerProof : outerNo residual previous)
      (outerOutput : OuterNoOutput residual previous outerProof)
      (innerProof : innerNo residual previous outerProof outerOutput)
      (current : Current residual previous outerProof outerOutput innerProof) :
      DependentDecisionOnNoYesClosedActive Previous outerYes outerNo
        OuterNoOutput innerYes innerNo Current residual

/-- Exhaustive yes/no refinement of the live payload of an active nested
cursor.  The bypass constructor is preserved literally. -/
inductive ActiveCursorDecision
    (Previous : Residual → Type uInput)
    (outerYes outerNo : (residual : Residual) → Previous residual → Prop)
    (OuterNoOutput : (residual : Residual) → (previous : Previous residual) →
      outerNo residual previous → Type uTarget)
    (innerYes innerNo : (residual : Residual) → (previous : Previous residual) →
      (outerProof : outerNo residual previous) →
      OuterNoOutput residual previous outerProof → Prop)
    (Current : (residual : Residual) → (previous : Previous residual) →
      (outerProof : outerNo residual previous) →
      (outerOutput : OuterNoOutput residual previous outerProof) →
      innerNo residual previous outerProof outerOutput → Type uStage)
    (yes no : (residual : Residual) → (previous : Previous residual) →
      (outerProof : outerNo residual previous) →
      (outerOutput : OuterNoOutput residual previous outerProof) →
      (innerProof : innerNo residual previous outerProof outerOutput) →
      Current residual previous outerProof outerOutput innerProof → Prop)
    (residual : Residual) : Type (max uInput uTarget uStage) where
  | outerYesBranch (previous : Previous residual) (proof : outerYes residual previous)
  | yesBranch (previous) (outerProof) (outerOutput) (innerProof) (current)
      (proof : yes residual previous outerProof outerOutput innerProof current)
  | noBranch (previous) (outerProof) (outerOutput) (innerProof) (current)
      (proof : no residual previous outerProof outerOutput innerProof current)

/-- Continue only the yes constructor of an `ActiveCursorDecision`.  The
outer bypass and the no constructor are retained literally; only the selected
yes constructor receives one new mathematical payload. -/
inductive ActiveCursorDecisionYesContinuation
    (Previous : Residual → Type uInput)
    (outerYes outerNo : (residual : Residual) → Previous residual → Prop)
    (OuterNoOutput : (residual : Residual) → (previous : Previous residual) →
      outerNo residual previous → Type uTarget)
    (innerYes innerNo : (residual : Residual) → (previous : Previous residual) →
      (outerProof : outerNo residual previous) →
      OuterNoOutput residual previous outerProof → Prop)
    (Current : (residual : Residual) → (previous : Previous residual) →
      (outerProof : outerNo residual previous) →
      (outerOutput : OuterNoOutput residual previous outerProof) →
      innerNo residual previous outerProof outerOutput → Type uStage)
    (yes no : (residual : Residual) → (previous : Previous residual) →
      (outerProof : outerNo residual previous) →
      (outerOutput : OuterNoOutput residual previous outerProof) →
      (innerProof : innerNo residual previous outerProof outerOutput) →
      Current residual previous outerProof outerOutput innerProof → Prop)
    (YesOutput : (residual : Residual) → (previous : Previous residual) →
      (outerProof : outerNo residual previous) →
      (outerOutput : OuterNoOutput residual previous outerProof) →
      (innerProof : innerNo residual previous outerProof outerOutput) →
      (current : Current residual previous outerProof outerOutput innerProof) →
      yes residual previous outerProof outerOutput innerProof current →
        Type uOccurrence)
    (residual : Residual) : Type (max uInput uTarget uStage uOccurrence) where
  | outerYesBranch (previous : Previous residual)
      (proof : outerYes residual previous)
  | yesBranch (previous) (outerProof) (outerOutput) (innerProof) (current)
      (proof : yes residual previous outerProof outerOutput innerProof current)
      (output : YesOutput residual previous outerProof outerOutput innerProof
        current proof)
  | noBranch (previous) (outerProof) (outerOutput) (innerProof) (current)
      (proof : no residual previous outerProof outerOutput innerProof current)

/-- Continue only the no constructor of an `ActiveCursorDecision`.  The
outer bypass and the yes constructor are retained literally; only the selected
no constructor receives one new mathematical payload. -/
inductive ActiveCursorDecisionNoContinuation
    (Previous : Residual → Type uInput)
    (outerYes outerNo : (residual : Residual) → Previous residual → Prop)
    (OuterNoOutput : (residual : Residual) → (previous : Previous residual) →
      outerNo residual previous → Type uTarget)
    (innerYes innerNo : (residual : Residual) → (previous : Previous residual) →
      (outerProof : outerNo residual previous) →
      OuterNoOutput residual previous outerProof → Prop)
    (Current : (residual : Residual) → (previous : Previous residual) →
      (outerProof : outerNo residual previous) →
      (outerOutput : OuterNoOutput residual previous outerProof) →
      innerNo residual previous outerProof outerOutput → Type uStage)
    (yes no : (residual : Residual) → (previous : Previous residual) →
      (outerProof : outerNo residual previous) →
      (outerOutput : OuterNoOutput residual previous outerProof) →
      (innerProof : innerNo residual previous outerProof outerOutput) →
      Current residual previous outerProof outerOutput innerProof → Prop)
    (NoOutput : (residual : Residual) → (previous : Previous residual) →
      (outerProof : outerNo residual previous) →
      (outerOutput : OuterNoOutput residual previous outerProof) →
      (innerProof : innerNo residual previous outerProof outerOutput) →
      (current : Current residual previous outerProof outerOutput innerProof) →
      no residual previous outerProof outerOutput innerProof current →
        Type uOccurrence)
    (residual : Residual) : Type (max uInput uTarget uStage uOccurrence) where
  | outerYesBranch (previous : Previous residual)
      (proof : outerYes residual previous)
  | yesBranch (previous) (outerProof) (outerOutput) (innerProof) (current)
      (proof : yes residual previous outerProof outerOutput innerProof current)
  | noBranch (previous) (outerProof) (outerOutput) (innerProof) (current)
      (proof : no residual previous outerProof outerOutput innerProof current)
      (output : NoOutput residual previous outerProof outerOutput innerProof
        current proof)

/-- The two already handled constructors of an active-cursor no
continuation.  This is framework-owned so an application can focus the sole
live no leaf without defining its own bypass sum. -/
inductive ActiveCursorDecisionNoContinuationBypass
    (Previous : Residual → Type uInput)
    (outerYes outerNo : (residual : Residual) → Previous residual → Prop)
    (OuterNoOutput : (residual : Residual) → (previous : Previous residual) →
      outerNo residual previous → Type uTarget)
    (innerYes innerNo : (residual : Residual) → (previous : Previous residual) →
      (outerProof : outerNo residual previous) →
      OuterNoOutput residual previous outerProof → Prop)
    (Current : (residual : Residual) → (previous : Previous residual) →
      (outerProof : outerNo residual previous) →
      (outerOutput : OuterNoOutput residual previous outerProof) →
      innerNo residual previous outerProof outerOutput → Type uStage)
    (yes no : (residual : Residual) → (previous : Previous residual) →
      (outerProof : outerNo residual previous) →
      (outerOutput : OuterNoOutput residual previous outerProof) →
      (innerProof : innerNo residual previous outerProof outerOutput) →
      Current residual previous outerProof outerOutput innerProof → Prop)
    (residual : Residual) : Type (max uInput uTarget uStage) where
  | outerYesBranch (previous : Previous residual)
      (proof : outerYes residual previous)
  | yesBranch (previous) (outerProof) (outerOutput) (innerProof) (current)
      (proof : yes residual previous outerProof outerOutput innerProof current)

/-- The sole live leaf of an active-cursor no continuation, including its
literal current output. -/
structure ActiveCursorDecisionNoContinuationActive
    (Previous : Residual → Type uInput)
    (outerNo : (residual : Residual) → Previous residual → Prop)
    (OuterNoOutput : (residual : Residual) → (previous : Previous residual) →
      outerNo residual previous → Type uTarget)
    (innerNo : (residual : Residual) → (previous : Previous residual) →
      (outerProof : outerNo residual previous) →
      OuterNoOutput residual previous outerProof → Prop)
    (Current : (residual : Residual) → (previous : Previous residual) →
      (outerProof : outerNo residual previous) →
      (outerOutput : OuterNoOutput residual previous outerProof) →
      innerNo residual previous outerProof outerOutput → Type uStage)
    (no : (residual : Residual) → (previous : Previous residual) →
      (outerProof : outerNo residual previous) →
      (outerOutput : OuterNoOutput residual previous outerProof) →
      (innerProof : innerNo residual previous outerProof outerOutput) →
      Current residual previous outerProof outerOutput innerProof → Prop)
    (NoOutput : (residual : Residual) → (previous : Previous residual) →
      (outerProof : outerNo residual previous) →
      (outerOutput : OuterNoOutput residual previous outerProof) →
      (innerProof : innerNo residual previous outerProof outerOutput) →
      (current : Current residual previous outerProof outerOutput innerProof) →
      no residual previous outerProof outerOutput innerProof current →
        Type uOccurrence)
    (residual : Residual) : Type (max uInput uTarget uStage uOccurrence) where
  previous : Previous residual
  outerProof : outerNo residual previous
  outerOutput : OuterNoOutput residual previous outerProof
  innerProof : innerNo residual previous outerProof outerOutput
  current : Current residual previous outerProof outerOutput innerProof
  proof : no residual previous outerProof outerOutput innerProof current
  output : NoOutput residual previous outerProof outerOutput innerProof current proof

/-! ## Focused decisions below an active yes continuation -/

/-- A reusable cursor with one active mathematical leaf and an opaque bundle
of already terminal or independently handled leaves. -/
inductive FocusedBranch
    (Bypass : Residual → Type uInput)
    (Active : Residual → Type uTarget)
    (residual : Residual) : Type (max uInput uTarget) where
  | bypass (data : Bypass residual)
  | active (data : Active residual)

/-- Framework-owned bypass data for a nested decision whose yes and no leaves
already carry outputs while only the no payload remains active. -/
inductive DependentDecisionOnNoNoAfterYesBypass
    (Previous : Residual → Type uInput)
    (outerYes outerNo : (residual : Residual) → Previous residual → Prop)
    (OuterNoOutput : (residual : Residual) → (previous : Previous residual) →
      outerNo residual previous → Type uTarget)
    (innerYes : (residual : Residual) → (previous : Previous residual) →
      (outerProof : outerNo residual previous) →
      OuterNoOutput residual previous outerProof → Prop)
    (YesOutput : (residual : Residual) → (previous : Previous residual) →
      (outerProof : outerNo residual previous) →
      (outerOutput : OuterNoOutput residual previous outerProof) →
      innerYes residual previous outerProof outerOutput → Type uStage)
    (residual : Residual) : Type (max uInput uTarget uStage) where
  | outerYesBranch (previous : Previous residual)
      (proof : outerYes residual previous)
  | innerYesBranch (previous : Previous residual)
      (outerProof : outerNo residual previous)
      (outerOutput : OuterNoOutput residual previous outerProof)
      (innerProof : innerYes residual previous outerProof outerOutput)
      (output : YesOutput residual previous outerProof outerOutput innerProof)

/-- Framework-owned exact data on the active inner-no leaf. Applications
consume this view but never repackage or transport it themselves. -/
structure DependentDecisionOnNoNoAfterYesActive
    (Previous : Residual → Type uInput)
    (outerNo : (residual : Residual) → Previous residual → Prop)
    (OuterNoOutput : (residual : Residual) → (previous : Previous residual) →
      outerNo residual previous → Type uTarget)
    (innerNo : (residual : Residual) → (previous : Previous residual) →
      (outerProof : outerNo residual previous) →
      OuterNoOutput residual previous outerProof → Prop)
    (Current : (residual : Residual) → (previous : Previous residual) →
      (outerProof : outerNo residual previous) →
      (outerOutput : OuterNoOutput residual previous outerProof) →
      innerNo residual previous outerProof outerOutput → Type uStage)
    (residual : Residual) : Type (max uInput uTarget uStage) where
  previous : Previous residual
  outerProof : outerNo residual previous
  outerOutput : OuterNoOutput residual previous outerProof
  innerProof : innerNo residual previous outerProof outerOutput
  current : Current residual previous outerProof outerOutput innerProof

namespace DependentDecisionOnNoNoAfterYesActive

/-- Framework-owned retrieval of the active inner-no payload.  This is the
generic replacement for application-specific active-output projections. -/
abbrev activeOutput
    {Previous : Residual → Type uInput}
    {outerNo : (residual : Residual) → Previous residual → Prop}
    {OuterNoOutput : (residual : Residual) → (previous : Previous residual) →
      outerNo residual previous → Type uTarget}
    {innerNo : (residual : Residual) → (previous : Previous residual) →
      (outerProof : outerNo residual previous) →
      OuterNoOutput residual previous outerProof → Prop}
    {Current : (residual : Residual) → (previous : Previous residual) →
      (outerProof : outerNo residual previous) →
      (outerOutput : OuterNoOutput residual previous outerProof) →
      innerNo residual previous outerProof outerOutput → Type uStage}
    {residual : Residual}
    (data : DependentDecisionOnNoNoAfterYesActive Previous outerNo
      OuterNoOutput innerNo Current residual) :
    Current residual data.previous data.outerProof data.outerOutput
      data.innerProof :=
  data.current

end DependentDecisionOnNoNoAfterYesActive

/-- An exhaustive decision on the active leaf of a `FocusedBranch`. -/
inductive FocusedBranchDecision
    (Bypass : Residual → Type uInput)
    (Active : Residual → Type uTarget)
    (yes no : (residual : Residual) → Active residual → Prop)
    (residual : Residual) : Type (max uInput uTarget) where
  | bypass (data : Bypass residual)
  | yesBranch (data : Active residual) (proof : yes residual data)
  | noBranch (data : Active residual) (proof : no residual data)

/-- Result of closing only the yes leaf of a focused decision. -/
inductive FocusedBranchDecisionYesClosed
    (Bypass : Residual → Type uInput)
    (Active : Residual → Type uTarget)
    (yes no : (residual : Residual) → Active residual → Prop)
    (residual : Residual) : Type (max uInput uTarget) where
  | bypass (data : Bypass residual)
  | activeNo (data : Active residual) (proof : no residual data)

/-- Result of closing only the live no leaf of a focused continuation.  Its
yes constructor is retained as an already handled sibling leaf. -/
inductive FocusedBranchDecisionNoClosed
    (Bypass : Residual → Type uInput)
    (Active : Residual → Type uTarget)
    (yes no : (residual : Residual) → Active residual → Prop)
    (residual : Residual) : Type (max uInput uTarget) where
  | bypass (data : Bypass residual)
  | activeYes (data : Active residual) (proof : yes residual data)

/-- Independent continuation of a focused decision's no leaf. -/
inductive FocusedBranchDecisionNoContinuation
    (Bypass : Residual → Type uInput)
    (Active : Residual → Type uTarget)
    (yes no : (residual : Residual) → Active residual → Prop)
    (Output : (residual : Residual) → (data : Active residual) →
      no residual data → Sort uStage)
    (residual : Residual) : Type (max uInput uTarget uStage) where
  | bypass (data : Bypass residual)
  | yesBranch (data : Active residual) (proof : yes residual data)
  | activeNo (data : Active residual) (proof : no residual data)
      (output : Output residual data proof)

/-- Framework-owned bypass for a new decision below the live leaf of a
focused-no continuation. -/
inductive FocusedBranchDecisionNoContinuationBypass
    (Bypass : Residual → Type uInput)
    (Active : Residual → Type uTarget)
    (yes no : (residual : Residual) → Active residual → Prop)
    (residual : Residual) : Type (max uInput uTarget) where
  | bypass (data : Bypass residual)
  | yesBranch (data : Active residual) (proof : yes residual data)

/-- The literal live leaf, including the output already attached by the
preceding focused-no continuation. -/
structure FocusedBranchDecisionNoContinuationActive
    (Active : Residual → Type uTarget)
    (no : (residual : Residual) → Active residual → Prop)
    (Output : (residual : Residual) → (data : Active residual) →
      no residual data → Sort uStage)
    (residual : Residual) : Type (max uTarget uStage) where
  data : Active residual
  proof : no residual data
  output : Output residual data proof

/-- Independent continuation of a focused decision's yes leaf. -/
inductive FocusedBranchDecisionYesContinuation
    (Bypass : Residual → Type uInput)
    (Active : Residual → Type uTarget)
    (yes no : (residual : Residual) → Active residual → Prop)
    (Output : (residual : Residual) → (data : Active residual) →
      yes residual data → Sort uStage)
    (residual : Residual) : Type (max uInput uTarget uStage) where
  | bypass (data : Bypass residual)
  | activeYes (data : Active residual) (proof : yes residual data)
      (output : Output residual data proof)
  | noBranch (data : Active residual) (proof : no residual data)

/-- Exhaustive decision on the payload already attached to a focused yes
continuation.  Core transports the bypass and untouched outer-no sibling
literally; applications provide only the next local predicate and its
complement. -/
inductive FocusedBranchYesContinuationDecision
    (Bypass : Residual → Type uInput)
    (Active : Residual → Type uTarget)
    (outerYes outerNo : (residual : Residual) → Active residual → Prop)
    (Output : (residual : Residual) → (data : Active residual) →
      outerYes residual data → Sort uStage)
    (innerYes innerNo : (residual : Residual) → (data : Active residual) →
      (outerProof : outerYes residual data) → Output residual data outerProof → Prop)
    (residual : Residual) : Type (max uInput uTarget uStage) where
  | bypass (data : Bypass residual)
  | activeYesYes (data : Active residual) (outerProof : outerYes residual data)
      (output : Output residual data outerProof)
      (innerProof : innerYes residual data outerProof output)
  | activeYesNo (data : Active residual) (outerProof : outerYes residual data)
      (output : Output residual data outerProof)
      (innerProof : innerNo residual data outerProof output)
  | noBranch (data : Active residual) (proof : outerNo residual data)

/-- Result of marking the inner-no leaf of a decision on a continued yes
payload terminal.  Every sibling and the terminal certificate are retained
literally in the accumulated ledger. -/
inductive FocusedBranchYesContinuationNoTerminal
    (Bypass : Residual → Type uInput)
    (Active : Residual → Type uTarget)
    (outerYes outerNo : (residual : Residual) → Active residual → Prop)
    (Output : (residual : Residual) → (data : Active residual) →
      outerYes residual data → Sort uStage)
    (innerYes innerNo : (residual : Residual) → (data : Active residual) →
      (outerProof : outerYes residual data) → Output residual data outerProof → Prop)
    (residual : Residual) : Type (max uInput uTarget uStage) where
  | bypass (data : Bypass residual)
  | activeYes (data : Active residual) (outerProof : outerYes residual data)
      (output : Output residual data outerProof)
      (innerProof : innerYes residual data outerProof output)
  | terminalNo (data : Active residual) (outerProof : outerYes residual data)
      (output : Output residual data outerProof)
      (innerProof : innerNo residual data outerProof output)
  | noBranch (data : Active residual) (proof : outerNo residual data)

/-- Decide one further predicate on the untouched no leaf of a focused
decision whose yes leaf already carries its successor payload.  This is the
generic carrier for two diagram branches that advance independently: the
outer yes payload is retained literally, while the outer no leaf is split
exhaustively without application-owned routing. -/
inductive FocusedBranchYesContinuationNoDecision
    (Bypass : Residual → Type uInput)
    (Active : Residual → Type uTarget)
    (outerYes outerNo : (residual : Residual) → Active residual → Prop)
    (OuterYesOutput : (residual : Residual) → (data : Active residual) →
      outerYes residual data → Sort uStage)
    (innerYes innerNo : (residual : Residual) →
      (data : Active residual) → outerNo residual data → Prop)
    (residual : Residual) : Type (max uInput uTarget uStage) where
  | bypass (data : Bypass residual)
  | outerYesBranch (data : Active residual)
      (proof : outerYes residual data)
      (output : OuterYesOutput residual data proof)
  | innerYesBranch (data : Active residual)
      (outerProof : outerNo residual data)
      (proof : innerYes residual data outerProof)
  | innerNoBranch (data : Active residual)
      (outerProof : outerNo residual data)
      (proof : innerNo residual data outerProof)

/-- Framework-owned terminal data retained after the already continued outer
yes leaf reaches a terminal manuscript node. -/
inductive FocusedBranchYesTerminalBypass
    (Bypass : Residual → Type uInput)
    (Active : Residual → Type uTarget)
    (outerYes : (residual : Residual) → Active residual → Prop)
    (OuterYesOutput : (residual : Residual) → (data : Active residual) →
      outerYes residual data → Sort uStage)
    (Terminal : (residual : Residual) → (data : Active residual) →
      (proof : outerYes residual data) →
      OuterYesOutput residual data proof → Sort uOccurrence)
    (residual : Residual) : Type
      (max uInput uTarget uStage uOccurrence) where
  | bypass (data : Bypass residual)
  | terminal (data : Active residual)
      (proof : outerYes residual data)
      (output : OuterYesOutput residual data proof)
      (certificate : Terminal residual data proof output)

/-- The exact surviving nested-no leaf after its two sibling leaves have
been terminalized or closed by the framework. -/
structure FocusedBranchNestedNoActive
    (Active : Residual → Type uTarget)
    (outerNo : (residual : Residual) → Active residual → Prop)
    (innerNo : (residual : Residual) →
      (data : Active residual) → outerNo residual data → Prop)
    (residual : Residual) : Type uTarget where
  data : Active residual
  outerProof : outerNo residual data
  innerProof : innerNo residual data outerProof

/-- A data-bearing successor on the active leaf of a reusable focused
branch.  The framework retains the active indices; the application output
contains only mathematics first proved at the successor node. -/
inductive FocusedBranchActiveContinuation
    (Bypass : Residual → Type uInput)
    (Active : Residual → Type uTarget)
    (Output : (residual : Residual) → Active residual → Type uStage)
    (residual : Residual) : Type (max uInput uTarget uStage) where
  | bypass (data : Bypass residual)
  | active (data : Active residual) (output : Output residual data)

/-- The type-level family of one existing `ActiveCursorDecisionYesContinuation`.
Packing these parameters once keeps downstream paper diamonds from repeating
transport plumbing. -/
structure ActiveCursorYesContinuationFamily (Residual : Type uResidual) where
  Previous : Residual → Type uInput
  outerYes : (residual : Residual) → Previous residual → Prop
  outerNo : (residual : Residual) → Previous residual → Prop
  OuterNoOutput : (residual : Residual) → (previous : Previous residual) →
    outerNo residual previous → Type uTarget
  innerYes : (residual : Residual) →
    (previous : Previous residual) →
    (outerProof : outerNo residual previous) →
    OuterNoOutput residual previous outerProof → Prop
  innerNo : (residual : Residual) →
    (previous : Previous residual) →
    (outerProof : outerNo residual previous) →
    OuterNoOutput residual previous outerProof → Prop
  Current : (residual : Residual) → (previous : Previous residual) →
    (outerProof : outerNo residual previous) →
    (outerOutput : OuterNoOutput residual previous outerProof) →
    innerNo residual previous outerProof outerOutput → Type uStage
  yes : (residual : Residual) → (previous : Previous residual) →
    (outerProof : outerNo residual previous) →
    (outerOutput : OuterNoOutput residual previous outerProof) →
    (innerProof : innerNo residual previous outerProof outerOutput) →
    Current residual previous outerProof outerOutput innerProof → Prop
  no : (residual : Residual) → (previous : Previous residual) →
    (outerProof : outerNo residual previous) →
    (outerOutput : OuterNoOutput residual previous outerProof) →
    (innerProof : innerNo residual previous outerProof outerOutput) →
    Current residual previous outerProof outerOutput innerProof → Prop
  YesOutput : (residual : Residual) → (previous : Previous residual) →
    (outerProof : outerNo residual previous) →
    (outerOutput : OuterNoOutput residual previous outerProof) →
    (innerProof : innerNo residual previous outerProof outerOutput) →
    (current : Current residual previous outerProof outerOutput innerProof) →
    yes residual previous outerProof outerOutput innerProof current →
      Type uOccurrence

namespace ActiveCursorYesContinuationFamily

variable {Residual : Type uResidual}
variable (family : ActiveCursorYesContinuationFamily Residual)

abbrev Source (residual : Residual) :=
  ActiveCursorDecisionYesContinuation family.Previous family.outerYes
    family.outerNo family.OuterNoOutput family.innerYes family.innerNo
    family.Current family.yes family.no family.YesOutput residual

/-- One exact populated yes leaf, bundled only inside Core. -/
structure ActiveData (residual : Residual) where
  previous : family.Previous residual
  outerProof : family.outerNo residual previous
  outerOutput : family.OuterNoOutput residual previous outerProof
  innerProof : family.innerNo residual previous outerProof outerOutput
  current : family.Current residual previous outerProof outerOutput innerProof
  yesProof : family.yes residual previous outerProof outerOutput innerProof current
  output : family.YesOutput residual previous outerProof outerOutput innerProof
    current yesProof

structure OuterBypassData (residual : Residual) where
  previous : family.Previous residual
  proof : family.outerYes residual previous

structure InitialNoData (residual : Residual) where
  previous : family.Previous residual
  outerProof : family.outerNo residual previous
  outerOutput : family.OuterNoOutput residual previous outerProof
  innerProof : family.innerNo residual previous outerProof outerOutput
  current : family.Current residual previous outerProof outerOutput innerProof
  proof : family.no residual previous outerProof outerOutput innerProof current

inductive Decision
    (nextYes nextNo : (residual : Residual) → family.ActiveData residual → Prop)
    (residual : Residual) where
  | outerBypass (data : family.OuterBypassData residual)
  | yesBranch (data : family.ActiveData residual)
      (proof : nextYes residual data)
  | noBranch (data : family.ActiveData residual)
      (proof : nextNo residual data)
  | initialNo (data : family.InitialNoData residual)

inductive NoTerminal
    (nextYes nextNo : (residual : Residual) → family.ActiveData residual → Prop)
    (residual : Residual) where
  | outerBypass (data : family.OuterBypassData residual)
  | activeYes (data : family.ActiveData residual)
      (proof : nextYes residual data)
  | terminalNo (data : family.ActiveData residual)
      (proof : nextNo residual data)
  | initialNo (data : family.InitialNoData residual)

inductive YesDecision
    (nextYes nextNo : (residual : Residual) → family.ActiveData residual → Prop)
    (finalYes finalNo : (residual : Residual) →
      (data : family.ActiveData residual) → nextYes residual data → Prop)
    (residual : Residual) where
  | outerBypass (data : family.OuterBypassData residual)
  | finalYes (data : family.ActiveData residual)
      (nextProof : nextYes residual data)
      (proof : finalYes residual data nextProof)
  | finalNo (data : family.ActiveData residual)
      (nextProof : nextYes residual data)
      (proof : finalNo residual data nextProof)
  | nextNo (data : family.ActiveData residual)
      (proof : nextNo residual data)
  | initialNo (data : family.InitialNoData residual)

inductive FinalYesClosed
    (nextYes nextNo : (residual : Residual) → family.ActiveData residual → Prop)
    (finalYes finalNo : (residual : Residual) →
      (data : family.ActiveData residual) → nextYes residual data → Prop)
    (residual : Residual) where
  | outerBypass (data : family.OuterBypassData residual)
  | activeNo (data : family.ActiveData residual)
      (nextProof : nextYes residual data)
      (proof : finalNo residual data nextProof)
  | nextNo (data : family.ActiveData residual)
      (proof : nextNo residual data)
  | initialNo (data : family.InitialNoData residual)

inductive FinalNoBypass
    (nextYes nextNo : (residual : Residual) → family.ActiveData residual → Prop)
    (finalYes finalNo : (residual : Residual) →
      (data : family.ActiveData residual) → nextYes residual data → Prop)
    (residual : Residual) where
  | outerBypass (data : family.OuterBypassData residual)
  | finalYes (data : family.ActiveData residual)
      (nextProof : nextYes residual data)
      (proof : finalYes residual data nextProof)
  | nextNo (data : family.ActiveData residual)
      (proof : nextNo residual data)
  | initialNo (data : family.InitialNoData residual)

structure FinalNoData
    (nextYes : (residual : Residual) → family.ActiveData residual → Prop)
    (finalNo : (residual : Residual) →
      (data : family.ActiveData residual) → nextYes residual data → Prop)
    (residual : Residual) where
  data : family.ActiveData residual
  nextProof : nextYes residual data
  proof : finalNo residual data nextProof

abbrev FinalNoActive
    (nextYes nextNo : (residual : Residual) → family.ActiveData residual → Prop)
    (finalYes finalNo : (residual : Residual) →
      (data : family.ActiveData residual) → nextYes residual data → Prop)
    (residual : Residual) :=
  FocusedBranch
    (family.FinalNoBypass nextYes nextNo finalYes finalNo)
    (family.FinalNoData nextYes finalNo) residual

end ActiveCursorYesContinuationFamily

/-- Reusable view of a populated yes continuation.  It packages only the
type parameters of the framework carrier; applications never provide routing
callbacks or predecessor values. -/
structure FocusedYesContinuationFamily (Residual : Type uResidual) where
  Bypass : Residual → Type uInput
  Active : Residual → Type uTarget
  outerYes : (residual : Residual) → Active residual → Prop
  outerNo : (residual : Residual) → Active residual → Prop
  Output : (residual : Residual) → (data : Active residual) →
    outerYes residual data → Type uStage

namespace FocusedYesContinuationFamily

variable {Residual : Type uResidual}
variable (family : FocusedYesContinuationFamily Residual)

abbrev Source := FocusedBranchDecisionYesContinuation family.Bypass family.Active
  family.outerYes family.outerNo family.Output

structure ActiveData (residual : Residual) where
  data : family.Active residual
  outerProof : family.outerYes residual data
  output : family.Output residual data outerProof

inductive Decision
    (nextYes nextNo : (residual : Residual) → family.ActiveData residual → Prop)
    (residual : Residual) where
  | bypass (data : family.Bypass residual)
  | yesBranch (data : family.ActiveData residual) (proof : nextYes residual data)
  | noBranch (data : family.ActiveData residual) (proof : nextNo residual data)
  | outerNo (data : family.Active residual) (proof : family.outerNo residual data)

inductive NoTerminal
    (nextYes nextNo : (residual : Residual) → family.ActiveData residual → Prop)
    (residual : Residual) where
  | bypass (data : family.Bypass residual)
  | activeYes (data : family.ActiveData residual) (proof : nextYes residual data)
  | terminalNo (data : family.ActiveData residual) (proof : nextNo residual data)
  | outerNo (data : family.Active residual) (proof : family.outerNo residual data)

inductive YesDecision
    (nextYes nextNo : (residual : Residual) → family.ActiveData residual → Prop)
    (finalYes finalNo : (residual : Residual) →
      (data : family.ActiveData residual) → nextYes residual data → Prop)
    (residual : Residual) where
  | bypass (data : family.Bypass residual)
  | finalYes (data : family.ActiveData residual) (nextProof : nextYes residual data)
      (proof : finalYes residual data nextProof)
  | finalNo (data : family.ActiveData residual) (nextProof : nextYes residual data)
      (proof : finalNo residual data nextProof)
  | nextNo (data : family.ActiveData residual) (proof : nextNo residual data)
  | outerNo (data : family.Active residual) (proof : family.outerNo residual data)

inductive FinalYesClosed
    (nextYes nextNo : (residual : Residual) → family.ActiveData residual → Prop)
    (finalYes finalNo : (residual : Residual) →
      (data : family.ActiveData residual) → nextYes residual data → Prop)
    (residual : Residual) where
  | bypass (data : family.Bypass residual)
  | activeNo (data : family.ActiveData residual) (nextProof : nextYes residual data)
      (proof : finalNo residual data nextProof)
  | nextNo (data : family.ActiveData residual) (proof : nextNo residual data)
  | outerNo (data : family.Active residual) (proof : family.outerNo residual data)

inductive FinalNoBypass
    (nextYes nextNo : (residual : Residual) → family.ActiveData residual → Prop)
    (finalYes finalNo : (residual : Residual) →
      (data : family.ActiveData residual) → nextYes residual data → Prop)
    (residual : Residual) where
  | bypass (data : family.Bypass residual)
  | finalYes (data : family.ActiveData residual) (nextProof : nextYes residual data)
      (proof : finalYes residual data nextProof)
  | nextNo (data : family.ActiveData residual) (proof : nextNo residual data)
  | outerNo (data : family.Active residual) (proof : family.outerNo residual data)

structure FinalNoData
    (nextYes : (residual : Residual) → family.ActiveData residual → Prop)
    (finalNo : (residual : Residual) →
      (data : family.ActiveData residual) → nextYes residual data → Prop)
    (residual : Residual) where
  data : family.ActiveData residual
  nextProof : nextYes residual data
  proof : finalNo residual data nextProof

abbrev FinalNoActive
    (nextYes nextNo : (residual : Residual) → family.ActiveData residual → Prop)
    (finalYes finalNo : (residual : Residual) →
      (data : family.ActiveData residual) → nextYes residual data → Prop) :=
  FocusedBranch (family.FinalNoBypass nextYes nextNo finalYes finalNo)
    (family.FinalNoData nextYes finalNo)

end FocusedYesContinuationFamily

/-- Package a canonical data producer as an exact-output stage.  Applications
name only the mathematical output; the framework supplies the retained value
and reflexive exactness certificate. -/
def StageNode.exact {Output : Residual → Sort uTarget}
    (produce : (residual : Residual) → Output residual) :
    StageNode (facts := facts)
      (fun residual => ExactHandoff (produce residual)) where
  produce := fun state => ExactHandoff.refl (produce state.residual)

/-- Build a theorem node by naming only the accumulated fact it consumes. -/
def Node.usingFact {required property : Residual → Prop}
    [Proofs.Contains required facts]
    (prove : (state : State Residual facts) →
      required state.residual → property state.residual) :
    Node (facts := facts) property where
  prove := fun state => prove state state.require

/-- Build a data-bearing node by naming only the accumulated proposition it
consumes. -/
def StageNode.usingFact {required : Residual → Prop}
    {Stage : Residual → Sort uTarget}
    [Proofs.Contains required facts]
    (produce : (state : State Residual facts) →
      required state.residual → Stage state.residual) :
    StageNode (facts := facts) Stage where
  produce := fun state => produce state state.require

/-- Build a data-bearing node by naming only its immediate certificate
dependency.  The complete earlier prefix remains accumulated but does not
appear in the application declaration. -/
noncomputable def StageNode.usingStage
    {Required : Residual → Sort uInput}
    {Stage : Residual → Sort uTarget}
    [Proofs.Contains (Available Required) facts]
    (produce : (state : State Residual facts) →
      Required state.residual → Stage state.residual) :
    StageNode (facts := facts) Stage where
  produce := fun state => produce state
    (Classical.choice (state.require (property := Available Required)))

/-- Retrieve one accumulated stage, construct its dependent successor from
that literal value, and retain both in one framework-owned payload.  The full
fact ledger remains in `State`; applications supply only the mathematical
successor producer. -/
noncomputable def StageNode.mapStage
    {Previous : Residual → Sort uInput}
    {Next : (residual : Residual) → Previous residual → Sort uTarget}
    [Proofs.Contains (Available Previous) facts]
    (produceNext : (residual : Residual) →
      (previous : Previous residual) → Next residual previous) :
    StageNode (facts := facts) (DependentSuccessor Previous Next) :=
  StageNode.usingStage (Required := Previous) fun state previous =>
    ⟨previous, produceNext state.residual previous⟩

/-- Retrieve one accumulated data stage and perform an exhaustive decision on
that exact value.  Retrieval, value retention, and branch packaging are
framework-owned; an application supplies only decidability and the theorem
for the complementary outcome. -/
noncomputable def StageNode.decideUsingStage
    {Previous : Residual → Type uInput}
    {yes no : (residual : Residual) → Previous residual → Prop}
    [Proofs.Contains (Available Previous) facts]
    (yesDecidable : (residual : Residual) → (previous : Previous residual) →
      Decidable (yes residual previous))
    (no_of_not_yes : (residual : Residual) → (previous : Previous residual) →
      ¬ yes residual previous → no residual previous) :
    StageNode (facts := facts) (DependentDecision Previous yes no) :=
  StageNode.usingStage (Required := Previous) fun state previous =>
    match yesDecidable state.residual previous with
    | .isTrue proof => .yesBranch previous proof
    | .isFalse absent =>
        .noBranch previous (no_of_not_yes state.residual previous absent)

/-- Close exactly the yes constructor of an accumulated dependent decision
and retain its no constructor as the sole successor.  The application proves
only the local contradiction; decision elimination and branch preservation
are framework-owned. -/
noncomputable def StageNode.closeDependentDecisionYes
    {Previous : Residual → Type uInput}
    {yes no : (residual : Residual) → Previous residual → Prop}
    [Proofs.Contains (Available (DependentDecision Previous yes no)) facts]
    (close : (residual : Residual) → (previous : Previous residual) →
      yes residual previous → False) :
    StageNode (facts := facts)
      (DependentDecisionYesClosed Previous yes no) :=
  StageNode.usingStage
    (Required := DependentDecision Previous yes no) fun state decision =>
      match decision with
      | .yesBranch previous proof =>
          (close state.residual previous proof).elim
      | .noBranch previous proof => ⟨previous, proof⟩

/-- Continue the yes constructor of an accumulated dependent decision with
one new mathematical producer.  Applications do not reconstruct the decision,
its predecessor, or its complementary branch. -/
noncomputable def StageNode.continueDependentDecisionYes
    {Previous : Residual → Type uInput}
    {yes no : (residual : Residual) → Previous residual → Prop}
    {Next : (residual : Residual) → (previous : Previous residual) →
      yes residual previous → Type uTarget}
    [Proofs.Contains
      (Available (DependentDecision Previous yes no)) facts]
    (produce : (residual : Residual) → (previous : Previous residual) →
      (proof : yes residual previous) → Next residual previous proof) :
    StageNode (facts := facts)
      (DependentDecisionYesContinuation Previous yes no Next) :=
  StageNode.usingStage
    (Required := DependentDecision Previous yes no) fun state decision =>
      match decision with
      | .yesBranch previous proof =>
          .yesBranch previous proof (produce state.residual previous proof)
      | .noBranch previous proof => .noBranch previous proof

/-- Continue the no constructor of an accumulated dependent decision with
one new mathematical producer. Applications supply only the negative-edge
mathematics; predecessor retrieval, branch elimination, and transport of the
untouched positive edge are framework-owned. -/
noncomputable def StageNode.continueDependentDecisionNo
    {Previous : Residual → Type uInput}
    {yes no : (residual : Residual) → Previous residual → Prop}
    {Next : (residual : Residual) → (previous : Previous residual) →
      no residual previous → Type uTarget}
    [Proofs.Contains
      (Available (DependentDecision Previous yes no)) facts]
    (produce : (residual : Residual) → (previous : Previous residual) →
      (proof : no residual previous) → Next residual previous proof) :
    StageNode (facts := facts)
      (DependentDecisionNoContinuation Previous yes no Next) :=
  StageNode.usingStage
    (Required := DependentDecision Previous yes no) fun state decision =>
      match decision with
      | .yesBranch previous proof => .yesBranch previous proof
      | .noBranch previous proof =>
          .noBranch previous proof (produce state.residual previous proof)

/-- Decide a new predicate only on the populated no constructor of an earlier
decision.  Applications provide the local decision and complement proof;
Core owns predecessor retrieval and preservation of the untouched leaf. -/
noncomputable def StageNode.decideOnDependentNoContinuation
    {Previous : Residual → Type uInput}
    {outerYes outerNo : (residual : Residual) → Previous residual → Prop}
    {OuterNoOutput : (residual : Residual) →
      (previous : Previous residual) → outerNo residual previous → Type uTarget}
    {innerYes innerNo : (residual : Residual) →
      (previous : Previous residual) →
      (outerProof : outerNo residual previous) →
      OuterNoOutput residual previous outerProof → Prop}
    [Proofs.Contains
      (Available (DependentDecisionNoContinuation Previous outerYes outerNo
        OuterNoOutput)) facts]
    (yesDecidable : (residual : Residual) → (previous : Previous residual) →
      (outerProof : outerNo residual previous) →
      (output : OuterNoOutput residual previous outerProof) →
      Decidable (innerYes residual previous outerProof output))
    (no_of_not_yes : (residual : Residual) →
      (previous : Previous residual) →
      (outerProof : outerNo residual previous) →
      (output : OuterNoOutput residual previous outerProof) →
      ¬innerYes residual previous outerProof output →
      innerNo residual previous outerProof output) :
    StageNode (facts := facts)
      (DependentDecisionOnNoContinuation Previous outerYes outerNo
        OuterNoOutput innerYes innerNo) :=
  StageNode.usingStage
    (Required := DependentDecisionNoContinuation Previous outerYes outerNo
      OuterNoOutput) fun state decision =>
      match decision with
      | .yesBranch previous proof => .outerYesBranch previous proof
      | .noBranch previous outerProof output =>
          match yesDecidable state.residual previous outerProof output with
          | .isTrue proof => .innerYesBranch previous outerProof output proof
          | .isFalse absent => .innerNoBranch previous outerProof output
              (no_of_not_yes state.residual previous outerProof output absent)

/-- Close only the inner yes leaf of a decision performed on an earlier no
continuation. Core owns leaf elimination and preservation of both unaffected
constructors. -/
noncomputable def StageNode.closeDependentDecisionOnNoYes
    {Previous : Residual → Type uInput}
    {outerYes outerNo : (residual : Residual) → Previous residual → Prop}
    {OuterNoOutput : (residual : Residual) →
      (previous : Previous residual) → outerNo residual previous → Type uTarget}
    {innerYes innerNo : (residual : Residual) →
      (previous : Previous residual) →
      (outerProof : outerNo residual previous) →
      OuterNoOutput residual previous outerProof → Prop}
    [Proofs.Contains
      (Available (DependentDecisionOnNoContinuation Previous outerYes outerNo
        OuterNoOutput innerYes innerNo)) facts]
    (close : (residual : Residual) → (previous : Previous residual) →
      (outerProof : outerNo residual previous) →
      (output : OuterNoOutput residual previous outerProof) →
      innerYes residual previous outerProof output → False) :
    StageNode (facts := facts)
      (DependentDecisionOnNoYesClosed Previous outerYes outerNo
        OuterNoOutput innerYes innerNo) :=
  StageNode.usingStage
    (Required := DependentDecisionOnNoContinuation Previous outerYes outerNo
      OuterNoOutput innerYes innerNo) fun state decision =>
      match decision with
      | .outerYesBranch previous proof => .outerYesBranch previous proof
      | .innerYesBranch previous outerProof output proof =>
          (close state.residual previous outerProof output proof).elim
      | .innerNoBranch previous outerProof output proof =>
          .innerNoBranch previous outerProof output proof

/-- Attach one new mathematical payload to the literal inner-yes leaf of a
decision made on an earlier no continuation.  Core owns all three branch
transports; applications provide only the selected leaf's local output. -/
noncomputable def StageNode.continueDependentDecisionOnNoYes
    {Previous : Residual → Type uInput}
    {outerYes outerNo : (residual : Residual) → Previous residual → Prop}
    {OuterNoOutput : (residual : Residual) →
      (previous : Previous residual) → outerNo residual previous → Type uTarget}
    {innerYes innerNo : (residual : Residual) →
      (previous : Previous residual) →
      (outerProof : outerNo residual previous) →
      OuterNoOutput residual previous outerProof → Prop}
    {YesOutput : (residual : Residual) →
      (previous : Previous residual) →
      (outerProof : outerNo residual previous) →
      (outerOutput : OuterNoOutput residual previous outerProof) →
      innerYes residual previous outerProof outerOutput → Type uStage}
    [Proofs.Contains
      (Available (DependentDecisionOnNoContinuation Previous outerYes outerNo
        OuterNoOutput innerYes innerNo)) facts]
    (produce : (residual : Residual) → (previous : Previous residual) →
      (outerProof : outerNo residual previous) →
      (outerOutput : OuterNoOutput residual previous outerProof) →
      (innerProof : innerYes residual previous outerProof outerOutput) →
        YesOutput residual previous outerProof outerOutput innerProof) :
    StageNode (facts := facts)
      (DependentDecisionOnNoYesContinuation Previous outerYes outerNo
        OuterNoOutput innerYes innerNo YesOutput) :=
  StageNode.usingStage
    (Required := DependentDecisionOnNoContinuation Previous outerYes outerNo
      OuterNoOutput innerYes innerNo) fun state decision =>
      match decision with
      | .outerYesBranch previous proof => .outerYesBranch previous proof
      | .innerYesBranch previous outerProof outerOutput innerProof =>
          .innerYesBranch previous outerProof outerOutput innerProof
            (produce state.residual previous outerProof outerOutput innerProof)
      | .innerNoBranch previous outerProof outerOutput innerProof =>
          .innerNoBranch previous outerProof outerOutput innerProof

/-- Continue the untouched inner-no edge after the inner-yes edge has already
received its exact successor payload. -/
noncomputable def StageNode.continueDependentDecisionOnNoNoAfterYes
    {Previous : Residual → Type uInput}
    {outerYes outerNo : (residual : Residual) → Previous residual → Prop}
    {OuterNoOutput : (residual : Residual) →
      (previous : Previous residual) → outerNo residual previous → Type uTarget}
    {innerYes innerNo : (residual : Residual) →
      (previous : Previous residual) →
      (outerProof : outerNo residual previous) →
      OuterNoOutput residual previous outerProof → Prop}
    {YesOutput : (residual : Residual) →
      (previous : Previous residual) →
      (outerProof : outerNo residual previous) →
      (outerOutput : OuterNoOutput residual previous outerProof) →
      innerYes residual previous outerProof outerOutput → Type uStage}
    {NoOutput : (residual : Residual) →
      (previous : Previous residual) →
      (outerProof : outerNo residual previous) →
      (outerOutput : OuterNoOutput residual previous outerProof) →
      innerNo residual previous outerProof outerOutput → Type uOccurrence}
    [Proofs.Contains
      (Available (DependentDecisionOnNoYesContinuation Previous outerYes outerNo
        OuterNoOutput innerYes innerNo YesOutput)) facts]
    (produce : (residual : Residual) → (previous : Previous residual) →
      (outerProof : outerNo residual previous) →
      (outerOutput : OuterNoOutput residual previous outerProof) →
      (innerProof : innerNo residual previous outerProof outerOutput) →
        NoOutput residual previous outerProof outerOutput innerProof) :
    StageNode (facts := facts)
      (DependentDecisionOnNoNoAfterYes Previous outerYes outerNo OuterNoOutput
        innerYes innerNo YesOutput NoOutput) :=
  StageNode.usingStage
    (Required := DependentDecisionOnNoYesContinuation Previous outerYes outerNo
      OuterNoOutput innerYes innerNo YesOutput) fun state continuation =>
      match continuation with
      | .outerYesBranch previous proof => .outerYesBranch previous proof
      | .innerYesBranch previous outerProof outerOutput innerProof output =>
          .innerYesBranch previous outerProof outerOutput innerProof output
      | .innerNoBranch previous outerProof outerOutput innerProof =>
          .innerNoBranch previous outerProof outerOutput innerProof
            (produce state.residual previous outerProof outerOutput innerProof)

/-- Replace only the payload on the inner-no leaf after both inner branches
have received their paper-local outputs.  The outer bypass and the populated
inner-yes sibling are transported literally, while the complete predecessor
stage remains available in the accumulated ledger. -/
noncomputable def StageNode.mapDependentDecisionOnNoNoAfterYes
    {Previous : Residual → Type uInput}
    {outerYes outerNo : (residual : Residual) → Previous residual → Prop}
    {OuterNoOutput : (residual : Residual) →
      (previous : Previous residual) → outerNo residual previous → Type uTarget}
    {innerYes innerNo : (residual : Residual) →
      (previous : Previous residual) →
      (outerProof : outerNo residual previous) →
      OuterNoOutput residual previous outerProof → Prop}
    {YesOutput : (residual : Residual) →
      (previous : Previous residual) →
      (outerProof : outerNo residual previous) →
      (outerOutput : OuterNoOutput residual previous outerProof) →
      innerYes residual previous outerProof outerOutput → Type uStage}
    {Current : (residual : Residual) →
      (previous : Previous residual) →
      (outerProof : outerNo residual previous) →
      (outerOutput : OuterNoOutput residual previous outerProof) →
      innerNo residual previous outerProof outerOutput → Type uOccurrence}
    {Next : (residual : Residual) →
      (previous : Previous residual) →
      (outerProof : outerNo residual previous) →
      (outerOutput : OuterNoOutput residual previous outerProof) →
      innerNo residual previous outerProof outerOutput → Type uNext}
    [Proofs.Contains
      (Available (DependentDecisionOnNoNoAfterYes Previous outerYes outerNo
        OuterNoOutput innerYes innerNo YesOutput Current)) facts]
    (produce : (residual : Residual) → (previous : Previous residual) →
      (outerProof : outerNo residual previous) →
      (outerOutput : OuterNoOutput residual previous outerProof) →
      (innerProof : innerNo residual previous outerProof outerOutput) →
      Current residual previous outerProof outerOutput innerProof →
        Next residual previous outerProof outerOutput innerProof) :
    StageNode (facts := facts)
      (DependentDecisionOnNoNoAfterYes Previous outerYes outerNo OuterNoOutput
        innerYes innerNo YesOutput Next) :=
  StageNode.usingStage
    (Required := DependentDecisionOnNoNoAfterYes Previous outerYes outerNo
      OuterNoOutput innerYes innerNo YesOutput Current) fun state continuation =>
      match continuation with
      | .outerYesBranch previous proof => .outerYesBranch previous proof
      | .innerYesBranch previous outerProof outerOutput innerProof output =>
          .innerYesBranch previous outerProof outerOutput innerProof output
      | .innerNoBranch previous outerProof outerOutput innerProof output =>
          .innerNoBranch previous outerProof outerOutput innerProof
            (produce state.residual previous outerProof outerOutput innerProof output)

/-- Advance the active inner-no leaf while retaining its exact predecessor
payload in a proof-relevant `DependentSuccessor`.  This is the standard
provenance-preserving mapper for facts needed many nodes later: applications
prove only `Next`, while Core stores the literal `Current` value beside it. -/
noncomputable def StageNode.accumulateDependentDecisionOnNoNoAfterYes
    {Previous : Residual → Type uInput}
    {outerYes outerNo : (residual : Residual) → Previous residual → Prop}
    {OuterNoOutput : (residual : Residual) → (previous : Previous residual) →
      outerNo residual previous → Type uTarget}
    {innerYes innerNo : (residual : Residual) →
      (previous : Previous residual) →
      (outerProof : outerNo residual previous) →
      OuterNoOutput residual previous outerProof → Prop}
    {YesOutput : (residual : Residual) → (previous : Previous residual) →
      (outerProof : outerNo residual previous) →
      (outerOutput : OuterNoOutput residual previous outerProof) →
      innerYes residual previous outerProof outerOutput → Type uStage}
    {Current : (residual : Residual) → (previous : Previous residual) →
      (outerProof : outerNo residual previous) →
      (outerOutput : OuterNoOutput residual previous outerProof) →
      innerNo residual previous outerProof outerOutput → Type uOccurrence}
    {Next : (residual : Residual) → (previous : Previous residual) →
      (outerProof : outerNo residual previous) →
      (outerOutput : OuterNoOutput residual previous outerProof) →
      (innerProof : innerNo residual previous outerProof outerOutput) →
      Current residual previous outerProof outerOutput innerProof → Type uNext}
    [Proofs.Contains (Available (DependentDecisionOnNoNoAfterYes Previous
      outerYes outerNo OuterNoOutput innerYes innerNo YesOutput Current)) facts]
    (produce : ∀ residual previous outerProof outerOutput innerProof current,
      Next residual previous outerProof outerOutput innerProof current) :
    StageNode (facts := facts)
      (DependentDecisionOnNoNoAfterYes Previous outerYes outerNo OuterNoOutput
        innerYes innerNo YesOutput
        (fun residual previous outerProof outerOutput innerProof =>
          DependentSuccessor
            (fun _ => Current residual previous outerProof outerOutput innerProof)
            (fun _ current => Next residual previous outerProof outerOutput
              innerProof current) residual)) :=
  StageNode.mapDependentDecisionOnNoNoAfterYes
    (Current := Current)
    (Next := fun residual previous outerProof outerOutput innerProof =>
      DependentSuccessor
        (fun _ => Current residual previous outerProof outerOutput innerProof)
        (fun _ current => Next residual previous outerProof outerOutput innerProof current)
        residual)
    fun residual previous outerProof outerOutput innerProof current =>
      ⟨current, produce residual previous outerProof outerOutput innerProof current⟩

/-- Start the reusable active cursor on the sole surviving inner-no leaf.
Core eliminates the already-closed shape and preserves the unrelated outer
leaf; application code supplies only the next paper-local mathematical
producer. -/
noncomputable def StageNode.continueDependentDecisionOnNoYesClosed
    {Previous : Residual → Type uInput}
    {outerYes outerNo : (residual : Residual) → Previous residual → Prop}
    {OuterNoOutput : (residual : Residual) →
      (previous : Previous residual) → outerNo residual previous → Type uTarget}
    {innerYes innerNo : (residual : Residual) →
      (previous : Previous residual) →
      (outerProof : outerNo residual previous) →
      OuterNoOutput residual previous outerProof → Prop}
    {Current : (residual : Residual) → (previous : Previous residual) →
      (outerProof : outerNo residual previous) →
      (outerOutput : OuterNoOutput residual previous outerProof) →
      innerNo residual previous outerProof outerOutput → Type uStage}
    [Proofs.Contains
      (Available (DependentDecisionOnNoYesClosed Previous outerYes outerNo
        OuterNoOutput innerYes innerNo)) facts]
    (produce : (residual : Residual) → (previous : Previous residual) →
      (outerProof : outerNo residual previous) →
      (outerOutput : OuterNoOutput residual previous outerProof) →
      (innerProof : innerNo residual previous outerProof outerOutput) →
        Current residual previous outerProof outerOutput innerProof) :
    StageNode (facts := facts)
      (DependentDecisionOnNoYesClosedActive Previous outerYes outerNo
        OuterNoOutput innerYes innerNo Current) :=
  StageNode.usingStage
    (Required := DependentDecisionOnNoYesClosed Previous outerYes outerNo
      OuterNoOutput innerYes innerNo) fun state decision =>
      match decision with
      | .outerYesBranch previous proof => .outerYesBranch previous proof
      | .innerNoBranch previous outerProof outerOutput innerProof =>
          .innerNoBranch previous outerProof outerOutput innerProof
            (produce state.residual previous outerProof outerOutput innerProof)

/-- Advance one paper node on an existing active cursor.  The producer sees
the literal latest output, while Core transports every branch proof and the
bypass constructor.  The consumed cursor remains in the accumulated ledger,
so the new active payload contains only the new node-local mathematics. -/
noncomputable def StageNode.mapDependentDecisionOnNoYesClosedActive
    {Previous : Residual → Type uInput}
    {outerYes outerNo : (residual : Residual) → Previous residual → Prop}
    {OuterNoOutput : (residual : Residual) →
      (previous : Previous residual) → outerNo residual previous → Type uTarget}
    {innerYes innerNo : (residual : Residual) →
      (previous : Previous residual) →
      (outerProof : outerNo residual previous) →
      OuterNoOutput residual previous outerProof → Prop}
    {Current : (residual : Residual) → (previous : Previous residual) →
      (outerProof : outerNo residual previous) →
      (outerOutput : OuterNoOutput residual previous outerProof) →
      innerNo residual previous outerProof outerOutput → Type uStage}
    {Next : (residual : Residual) → (previous : Previous residual) →
      (outerProof : outerNo residual previous) →
      (outerOutput : OuterNoOutput residual previous outerProof) →
      innerNo residual previous outerProof outerOutput → Type uOccurrence}
    [Proofs.Contains
      (Available (DependentDecisionOnNoYesClosedActive Previous outerYes outerNo
        OuterNoOutput innerYes innerNo Current)) facts]
    (produce : (residual : Residual) → (previous : Previous residual) →
      (outerProof : outerNo residual previous) →
      (outerOutput : OuterNoOutput residual previous outerProof) →
      (innerProof : innerNo residual previous outerProof outerOutput) →
      Current residual previous outerProof outerOutput innerProof →
        Next residual previous outerProof outerOutput innerProof) :
    StageNode (facts := facts)
      (DependentDecisionOnNoYesClosedActive Previous outerYes outerNo
        OuterNoOutput innerYes innerNo Next) :=
  StageNode.usingStage
    (Required := DependentDecisionOnNoYesClosedActive Previous outerYes outerNo
      OuterNoOutput innerYes innerNo Current) fun state cursor =>
      match cursor with
      | .outerYesBranch previous proof => .outerYesBranch previous proof
      | .innerNoBranch previous outerProof outerOutput innerProof current =>
          .innerNoBranch previous outerProof outerOutput innerProof
            (produce state.residual previous outerProof outerOutput innerProof current)

/-- Decide one new paper predicate on the live payload of an active cursor.
Core owns the branch carrier and preserves the bypass and complete history. -/
noncomputable def StageNode.decideDependentDecisionOnNoYesClosedActive
    {Previous : Residual → Type uInput}
    {outerYes outerNo : (residual : Residual) → Previous residual → Prop}
    {OuterNoOutput : (residual : Residual) → (previous : Previous residual) →
      outerNo residual previous → Type uTarget}
    {innerYes innerNo : (residual : Residual) → (previous : Previous residual) →
      (outerProof : outerNo residual previous) →
      OuterNoOutput residual previous outerProof → Prop}
    {Current : (residual : Residual) → (previous : Previous residual) →
      (outerProof : outerNo residual previous) →
      (outerOutput : OuterNoOutput residual previous outerProof) →
      innerNo residual previous outerProof outerOutput → Type uStage}
    {yes no : (residual : Residual) → (previous : Previous residual) →
      (outerProof : outerNo residual previous) →
      (outerOutput : OuterNoOutput residual previous outerProof) →
      (innerProof : innerNo residual previous outerProof outerOutput) →
      Current residual previous outerProof outerOutput innerProof → Prop}
    [Proofs.Contains (Available (DependentDecisionOnNoYesClosedActive Previous
      outerYes outerNo OuterNoOutput innerYes innerNo Current)) facts]
    (decideYes : ∀ residual previous outerProof outerOutput innerProof current,
      Decidable (yes residual previous outerProof outerOutput innerProof current))
    (noOfNotYes : ∀ residual previous outerProof outerOutput innerProof current,
      ¬ yes residual previous outerProof outerOutput innerProof current →
      no residual previous outerProof outerOutput innerProof current) :
    StageNode (facts := facts) (ActiveCursorDecision Previous outerYes outerNo
      OuterNoOutput innerYes innerNo Current yes no) :=
  StageNode.usingStage
    (Required := DependentDecisionOnNoYesClosedActive Previous outerYes outerNo
      OuterNoOutput innerYes innerNo Current) fun state cursor =>
    match cursor with
    | DependentDecisionOnNoYesClosedActive.outerYesBranch previous proof =>
        ActiveCursorDecision.outerYesBranch previous proof
    | DependentDecisionOnNoYesClosedActive.innerNoBranch previous outerProof outerOutput innerProof current =>
        match decideYes state.residual previous outerProof outerOutput innerProof current with
        | .isTrue proof => ActiveCursorDecision.yesBranch previous outerProof outerOutput innerProof current proof
        | .isFalse absent => ActiveCursorDecision.noBranch previous outerProof outerOutput innerProof current
            (noOfNotYes state.residual previous outerProof outerOutput innerProof current absent)

/-- Append one payload only to the yes constructor of an active-cursor
decision.  Core owns elimination of the decision and transports the outer
bypass and complementary no constructor without application callbacks. -/
noncomputable def StageNode.continueActiveCursorDecisionYes
    {Previous : Residual → Type uInput}
    {outerYes outerNo : (residual : Residual) → Previous residual → Prop}
    {OuterNoOutput : (residual : Residual) → (previous : Previous residual) →
      outerNo residual previous → Type uTarget}
    {innerYes innerNo : (residual : Residual) → (previous : Previous residual) →
      (outerProof : outerNo residual previous) →
      OuterNoOutput residual previous outerProof → Prop}
    {Current : (residual : Residual) → (previous : Previous residual) →
      (outerProof : outerNo residual previous) →
      (outerOutput : OuterNoOutput residual previous outerProof) →
      innerNo residual previous outerProof outerOutput → Type uStage}
    {yes no : (residual : Residual) → (previous : Previous residual) →
      (outerProof : outerNo residual previous) →
      (outerOutput : OuterNoOutput residual previous outerProof) →
      (innerProof : innerNo residual previous outerProof outerOutput) →
      Current residual previous outerProof outerOutput innerProof → Prop}
    {YesOutput : (residual : Residual) → (previous : Previous residual) →
      (outerProof : outerNo residual previous) →
      (outerOutput : OuterNoOutput residual previous outerProof) →
      (innerProof : innerNo residual previous outerProof outerOutput) →
      (current : Current residual previous outerProof outerOutput innerProof) →
      yes residual previous outerProof outerOutput innerProof current →
        Type uOccurrence}
    [Proofs.Contains (Available (ActiveCursorDecision Previous outerYes outerNo
      OuterNoOutput innerYes innerNo Current yes no)) facts]
    (produce : (residual : Residual) → (previous : Previous residual) →
      (outerProof : outerNo residual previous) →
      (outerOutput : OuterNoOutput residual previous outerProof) →
      (innerProof : innerNo residual previous outerProof outerOutput) →
      (current : Current residual previous outerProof outerOutput innerProof) →
      (proof : yes residual previous outerProof outerOutput innerProof current) →
        YesOutput residual previous outerProof outerOutput innerProof current proof) :
    StageNode (facts := facts) (ActiveCursorDecisionYesContinuation Previous
      outerYes outerNo OuterNoOutput innerYes innerNo Current yes no YesOutput) :=
  StageNode.usingStage
    (Required := ActiveCursorDecision Previous outerYes outerNo OuterNoOutput
      innerYes innerNo Current yes no) fun state decision =>
    match decision with
    | .outerYesBranch previous proof => .outerYesBranch previous proof
    | .yesBranch previous outerProof outerOutput innerProof current proof =>
        .yesBranch previous outerProof outerOutput innerProof current proof
          (produce state.residual previous outerProof outerOutput innerProof
            current proof)
    | .noBranch previous outerProof outerOutput innerProof current proof =>
        .noBranch previous outerProof outerOutput innerProof current proof

/-- Append one payload only to the no constructor of an active-cursor
decision.  This executor is independent of the yes continuation, so two
successor nodes can be accumulated from the same literal decision stage. -/
noncomputable def StageNode.continueActiveCursorDecisionNo
    {Previous : Residual → Type uInput}
    {outerYes outerNo : (residual : Residual) → Previous residual → Prop}
    {OuterNoOutput : (residual : Residual) → (previous : Previous residual) →
      outerNo residual previous → Type uTarget}
    {innerYes innerNo : (residual : Residual) → (previous : Previous residual) →
      (outerProof : outerNo residual previous) →
      OuterNoOutput residual previous outerProof → Prop}
    {Current : (residual : Residual) → (previous : Previous residual) →
      (outerProof : outerNo residual previous) →
      (outerOutput : OuterNoOutput residual previous outerProof) →
      innerNo residual previous outerProof outerOutput → Type uStage}
    {yes no : (residual : Residual) → (previous : Previous residual) →
      (outerProof : outerNo residual previous) →
      (outerOutput : OuterNoOutput residual previous outerProof) →
      (innerProof : innerNo residual previous outerProof outerOutput) →
      Current residual previous outerProof outerOutput innerProof → Prop}
    {NoOutput : (residual : Residual) → (previous : Previous residual) →
      (outerProof : outerNo residual previous) →
      (outerOutput : OuterNoOutput residual previous outerProof) →
      (innerProof : innerNo residual previous outerProof outerOutput) →
      (current : Current residual previous outerProof outerOutput innerProof) →
      no residual previous outerProof outerOutput innerProof current →
        Type uOccurrence}
    [Proofs.Contains (Available (ActiveCursorDecision Previous outerYes outerNo
      OuterNoOutput innerYes innerNo Current yes no)) facts]
    (produce : (residual : Residual) → (previous : Previous residual) →
      (outerProof : outerNo residual previous) →
      (outerOutput : OuterNoOutput residual previous outerProof) →
      (innerProof : innerNo residual previous outerProof outerOutput) →
      (current : Current residual previous outerProof outerOutput innerProof) →
      (proof : no residual previous outerProof outerOutput innerProof current) →
        NoOutput residual previous outerProof outerOutput innerProof current proof) :
    StageNode (facts := facts) (ActiveCursorDecisionNoContinuation Previous
      outerYes outerNo OuterNoOutput innerYes innerNo Current yes no NoOutput) :=
  StageNode.usingStage
    (Required := ActiveCursorDecision Previous outerYes outerNo OuterNoOutput
      innerYes innerNo Current yes no) fun state decision =>
    match decision with
    | .outerYesBranch previous proof => .outerYesBranch previous proof
    | .yesBranch previous outerProof outerOutput innerProof current proof =>
        .yesBranch previous outerProof outerOutput innerProof current proof
    | .noBranch previous outerProof outerOutput innerProof current proof =>
        .noBranch previous outerProof outerOutput innerProof current proof
          (produce state.residual previous outerProof outerOutput innerProof
            current proof)

/-- Replace the mathematical payload on the literal no continuation of an
active cursor. Both bypass constructors and every branch proof are preserved
by Core; applications supply only the next local payload. -/
noncomputable def StageNode.mapActiveCursorDecisionNoContinuation
    {Previous : Residual → Type uInput}
    {outerYes outerNo : (residual : Residual) → Previous residual → Prop}
    {OuterNoOutput : (residual : Residual) → (previous : Previous residual) →
      outerNo residual previous → Type uTarget}
    {innerYes innerNo : (residual : Residual) → (previous : Previous residual) →
      (outerProof : outerNo residual previous) →
      OuterNoOutput residual previous outerProof → Prop}
    {Current : (residual : Residual) → (previous : Previous residual) →
      (outerProof : outerNo residual previous) →
      (outerOutput : OuterNoOutput residual previous outerProof) →
      innerNo residual previous outerProof outerOutput → Type uStage}
    {yes no : (residual : Residual) → (previous : Previous residual) →
      (outerProof : outerNo residual previous) →
      (outerOutput : OuterNoOutput residual previous outerProof) →
      (innerProof : innerNo residual previous outerProof outerOutput) →
      Current residual previous outerProof outerOutput innerProof → Prop}
    {Output : (residual : Residual) → (previous : Previous residual) →
      (outerProof : outerNo residual previous) →
      (outerOutput : OuterNoOutput residual previous outerProof) →
      (innerProof : innerNo residual previous outerProof outerOutput) →
      (current : Current residual previous outerProof outerOutput innerProof) →
      no residual previous outerProof outerOutput innerProof current →
        Type uOccurrence}
    {Next : (residual : Residual) → (previous : Previous residual) →
      (outerProof : outerNo residual previous) →
      (outerOutput : OuterNoOutput residual previous outerProof) →
      (innerProof : innerNo residual previous outerProof outerOutput) →
      (current : Current residual previous outerProof outerOutput innerProof) →
      no residual previous outerProof outerOutput innerProof current →
        Type uNext}
    [Proofs.Contains (Available (ActiveCursorDecisionNoContinuation Previous
      outerYes outerNo OuterNoOutput innerYes innerNo Current yes no Output)) facts]
    (produce : (residual : Residual) → (previous : Previous residual) →
      (outerProof : outerNo residual previous) →
      (outerOutput : OuterNoOutput residual previous outerProof) →
      (innerProof : innerNo residual previous outerProof outerOutput) →
      (current : Current residual previous outerProof outerOutput innerProof) →
      (proof : no residual previous outerProof outerOutput innerProof current) →
      Output residual previous outerProof outerOutput innerProof current proof →
        Next residual previous outerProof outerOutput innerProof current proof) :
    StageNode (facts := facts) (ActiveCursorDecisionNoContinuation Previous
      outerYes outerNo OuterNoOutput innerYes innerNo Current yes no Next) :=
  StageNode.usingStage
    (Required := ActiveCursorDecisionNoContinuation Previous outerYes outerNo
      OuterNoOutput innerYes innerNo Current yes no Output)
      fun state continuation =>
        match continuation with
        | .outerYesBranch previous proof => .outerYesBranch previous proof
        | .yesBranch previous outerProof outerOutput innerProof current proof =>
            .yesBranch previous outerProof outerOutput innerProof current proof
        | .noBranch previous outerProof outerOutput innerProof current proof output =>
            .noBranch previous outerProof outerOutput innerProof current proof
              (produce state.residual previous outerProof outerOutput innerProof
                current proof output)

/-- Focus and decide a predicate on the sole live leaf of an active-cursor no
continuation. Core owns the bypass sum and retains the literal active data. -/
noncomputable def StageNode.decideActiveCursorDecisionNoContinuation
    {Previous : Residual → Type uInput}
    {outerYes outerNo : (residual : Residual) → Previous residual → Prop}
    {OuterNoOutput : (residual : Residual) → (previous : Previous residual) →
      outerNo residual previous → Type uTarget}
    {innerYes innerNo : (residual : Residual) → (previous : Previous residual) →
      (outerProof : outerNo residual previous) →
      OuterNoOutput residual previous outerProof → Prop}
    {Current : (residual : Residual) → (previous : Previous residual) →
      (outerProof : outerNo residual previous) →
      (outerOutput : OuterNoOutput residual previous outerProof) →
      innerNo residual previous outerProof outerOutput → Type uStage}
    {yes no : (residual : Residual) → (previous : Previous residual) →
      (outerProof : outerNo residual previous) →
      (outerOutput : OuterNoOutput residual previous outerProof) →
      (innerProof : innerNo residual previous outerProof outerOutput) →
      Current residual previous outerProof outerOutput innerProof → Prop}
    {Output : (residual : Residual) → (previous : Previous residual) →
      (outerProof : outerNo residual previous) →
      (outerOutput : OuterNoOutput residual previous outerProof) →
      (innerProof : innerNo residual previous outerProof outerOutput) →
      (current : Current residual previous outerProof outerOutput innerProof) →
      no residual previous outerProof outerOutput innerProof current →
        Type uOccurrence}
    {nextYes nextNo : (residual : Residual) →
      ActiveCursorDecisionNoContinuationActive Previous outerNo OuterNoOutput
        innerNo Current no Output residual → Prop}
    [Proofs.Contains (Available (ActiveCursorDecisionNoContinuation Previous
      outerYes outerNo OuterNoOutput innerYes innerNo Current yes no Output)) facts]
    (decideYes : ∀ residual active, Decidable (nextYes residual active))
    (noOfNotYes : ∀ residual active,
      ¬ nextYes residual active → nextNo residual active) :
    StageNode (facts := facts) (FocusedBranchDecision
      (ActiveCursorDecisionNoContinuationBypass Previous outerYes outerNo
        OuterNoOutput innerYes innerNo Current yes no)
      (ActiveCursorDecisionNoContinuationActive Previous outerNo OuterNoOutput
        innerNo Current no Output) nextYes nextNo) :=
  StageNode.usingStage
    (Required := ActiveCursorDecisionNoContinuation Previous outerYes outerNo
      OuterNoOutput innerYes innerNo Current yes no Output)
      fun state continuation =>
        match continuation with
        | .outerYesBranch previous proof =>
            .bypass (.outerYesBranch previous proof)
        | .yesBranch previous outerProof outerOutput innerProof current proof =>
            .bypass (.yesBranch previous outerProof outerOutput innerProof
              current proof)
        | .noBranch previous outerProof outerOutput innerProof current proof output =>
            let active :
                ActiveCursorDecisionNoContinuationActive Previous outerNo
                  OuterNoOutput innerNo Current no Output state.residual := {
              previous := previous
              outerProof := outerProof
              outerOutput := outerOutput
              innerProof := innerProof
              current := current
              proof := proof
              output := output
            }
            match decideYes state.residual active with
            | .isTrue nextProof => .yesBranch active nextProof
            | .isFalse absent =>
                .noBranch active (noOfNotYes state.residual active absent)

/-- Focus and exhaustively decide a new predicate on the sole live leaf of a
focused-no continuation. Core retains both earlier bypass constructors and
the exact attached predecessor output. -/
noncomputable def StageNode.decideFocusedBranchNoContinuation
    {Bypass : Residual → Type uInput}
    {Active : Residual → Type uTarget}
    {yes no : (residual : Residual) → Active residual → Prop}
    {Output : (residual : Residual) → (data : Active residual) →
      no residual data → Sort uStage}
    {nextYes nextNo : (residual : Residual) →
      FocusedBranchDecisionNoContinuationActive Active no Output residual → Prop}
    [Proofs.Contains (Available
      (FocusedBranchDecisionNoContinuation Bypass Active yes no Output)) facts]
    (decideYes : ∀ residual active, Decidable (nextYes residual active))
    (noOfNotYes : ∀ residual active,
      ¬ nextYes residual active → nextNo residual active) :
    StageNode (facts := facts) (FocusedBranchDecision
      (FocusedBranchDecisionNoContinuationBypass Bypass Active yes no)
      (FocusedBranchDecisionNoContinuationActive Active no Output)
      nextYes nextNo) :=
  StageNode.usingStage
    (Required := FocusedBranchDecisionNoContinuation Bypass Active yes no Output)
      fun state continuation =>
        match continuation with
        | .bypass data => .bypass (.bypass data)
        | .yesBranch data proof => .bypass (.yesBranch data proof)
        | .activeNo data proof output =>
            let active : FocusedBranchDecisionNoContinuationActive
                Active no Output state.residual := ⟨data, proof, output⟩
            match decideYes state.residual active with
            | .isTrue nextProof => .yesBranch active nextProof
            | .isFalse absent =>
                .noBranch active (noOfNotYes state.residual active absent)

/-- Replace the latest payload on the yes continuation with one new
branch-local payload.  The preceding continuation remains available in the
single accumulated ledger; the outer bypass and no constructor are once again
transported literally. -/
noncomputable def StageNode.mapActiveCursorDecisionYesContinuation
    {Previous : Residual → Type uInput}
    {outerYes outerNo : (residual : Residual) → Previous residual → Prop}
    {OuterNoOutput : (residual : Residual) → (previous : Previous residual) →
      outerNo residual previous → Type uTarget}
    {innerYes innerNo : (residual : Residual) → (previous : Previous residual) →
      (outerProof : outerNo residual previous) →
      OuterNoOutput residual previous outerProof → Prop}
    {Current : (residual : Residual) → (previous : Previous residual) →
      (outerProof : outerNo residual previous) →
      (outerOutput : OuterNoOutput residual previous outerProof) →
      innerNo residual previous outerProof outerOutput → Type uStage}
    {yes no : (residual : Residual) → (previous : Previous residual) →
      (outerProof : outerNo residual previous) →
      (outerOutput : OuterNoOutput residual previous outerProof) →
      (innerProof : innerNo residual previous outerProof outerOutput) →
      Current residual previous outerProof outerOutput innerProof → Prop}
    {YesOutput : (residual : Residual) →
      (previous : Previous residual) →
      (outerProof : outerNo residual previous) →
      (outerOutput : OuterNoOutput residual previous outerProof) →
      (innerProof : innerNo residual previous outerProof outerOutput) →
      (current : Current residual previous outerProof outerOutput innerProof) →
      yes residual previous outerProof outerOutput innerProof current →
        Type uOccurrence}
    {NextOutput : (residual : Residual) →
      (previous : Previous residual) →
      (outerProof : outerNo residual previous) →
      (outerOutput : OuterNoOutput residual previous outerProof) →
      (innerProof : innerNo residual previous outerProof outerOutput) →
      (current : Current residual previous outerProof outerOutput innerProof) →
      yes residual previous outerProof outerOutput innerProof current →
        Type uNext}
    [Proofs.Contains (Available (ActiveCursorDecisionYesContinuation Previous
      outerYes outerNo OuterNoOutput innerYes innerNo Current yes no YesOutput)) facts]
    (produce : (residual : Residual) → (previous : Previous residual) →
      (outerProof : outerNo residual previous) →
      (outerOutput : OuterNoOutput residual previous outerProof) →
      (innerProof : innerNo residual previous outerProof outerOutput) →
      (current : Current residual previous outerProof outerOutput innerProof) →
      (proof : yes residual previous outerProof outerOutput innerProof current) →
      YesOutput residual previous outerProof outerOutput innerProof current proof →
        NextOutput residual previous outerProof outerOutput innerProof current proof) :
    StageNode (facts := facts) (ActiveCursorDecisionYesContinuation Previous
      outerYes outerNo OuterNoOutput innerYes innerNo Current yes no NextOutput) :=
  StageNode.usingStage
    (Required := ActiveCursorDecisionYesContinuation Previous outerYes outerNo
      OuterNoOutput innerYes innerNo Current yes no YesOutput)
      fun state continuation =>
    match continuation with
    | .outerYesBranch previous proof => .outerYesBranch previous proof
    | .yesBranch previous outerProof outerOutput innerProof current proof output =>
        .yesBranch previous outerProof outerOutput innerProof current proof
          (produce state.residual previous outerProof outerOutput innerProof
            current proof output)
    | .noBranch previous outerProof outerOutput innerProof current proof =>
        .noBranch previous outerProof outerOutput innerProof current proof

/-- Decide a new paper predicate on the exact payload of an already continued
active yes leaf. -/
noncomputable def StageNode.decideActiveCursorYesContinuation
    (family : ActiveCursorYesContinuationFamily Residual)
    {nextYes nextNo : (residual : Residual) → family.ActiveData residual → Prop}
    [Proofs.Contains (Available family.Source) facts]
    (decideYes : ∀ residual data, Decidable (nextYes residual data))
    (noOfNotYes : ∀ residual data,
      ¬ nextYes residual data → nextNo residual data) :
    StageNode (facts := facts) (family.Decision nextYes nextNo) :=
  StageNode.usingStage (Required := family.Source) fun state source =>
    match source with
    | .outerYesBranch previous proof =>
        .outerBypass ⟨previous, proof⟩
    | .yesBranch previous outerProof outerOutput innerProof current yesProof output =>
        let data : family.ActiveData state.residual :=
          ⟨previous, outerProof, outerOutput, innerProof, current, yesProof, output⟩
        match decideYes state.residual data with
        | .isTrue proof => .yesBranch data proof
        | .isFalse absent => .noBranch data (noOfNotYes state.residual data absent)
    | .noBranch previous outerProof outerOutput innerProof current proof =>
        .initialNo ⟨previous, outerProof, outerOutput, innerProof, current, proof⟩

/-- Mark only the negative leaf of a focused decision terminal. -/
noncomputable def StageNode.markActiveCursorYesContinuationNoTerminal
    (family : ActiveCursorYesContinuationFamily Residual)
    {nextYes nextNo : (residual : Residual) → family.ActiveData residual → Prop}
    [Proofs.Contains (Available (family.Decision nextYes nextNo)) facts] :
    StageNode (facts := facts) (family.NoTerminal nextYes nextNo) :=
  StageNode.usingStage (Required := family.Decision nextYes nextNo)
    fun _state decision =>
      match decision with
      | .outerBypass data => .outerBypass data
      | .yesBranch data proof => .activeYes data proof
      | .noBranch data proof => .terminalNo data proof
      | .initialNo data => .initialNo data

/-- Decide one further predicate on the positive leaf of the first decision.
The first negative leaf remains an independent sibling. -/
noncomputable def StageNode.decideActiveCursorYesContinuationYes
    (family : ActiveCursorYesContinuationFamily Residual)
    {nextYes nextNo : (residual : Residual) → family.ActiveData residual → Prop}
    {finalYes finalNo : (residual : Residual) →
      (data : family.ActiveData residual) → nextYes residual data → Prop}
    [Proofs.Contains (Available (family.Decision nextYes nextNo)) facts]
    (decideYes : ∀ residual data nextProof,
      Decidable (finalYes residual data nextProof))
    (noOfNotYes : ∀ residual data nextProof,
      ¬ finalYes residual data nextProof → finalNo residual data nextProof) :
    StageNode (facts := facts)
      (family.YesDecision nextYes nextNo finalYes finalNo) :=
  StageNode.usingStage (Required := family.Decision nextYes nextNo)
    fun state decision =>
      match decision with
      | .outerBypass data => .outerBypass data
      | .yesBranch data nextProof =>
          match decideYes state.residual data nextProof with
          | .isTrue proof => .finalYes data nextProof proof
          | .isFalse absent =>
              .finalNo data nextProof
                (noOfNotYes state.residual data nextProof absent)
      | .noBranch data proof => .nextNo data proof
      | .initialNo data => .initialNo data

/-- Close only the final positive leaf of a focused nested decision. -/
noncomputable def StageNode.closeActiveCursorYesContinuationFinalYes
    (family : ActiveCursorYesContinuationFamily Residual)
    {nextYes nextNo : (residual : Residual) → family.ActiveData residual → Prop}
    {finalYes finalNo : (residual : Residual) →
      (data : family.ActiveData residual) → nextYes residual data → Prop}
    [Proofs.Contains
      (Available (family.YesDecision nextYes nextNo finalYes finalNo)) facts]
    (close : ∀ residual data nextProof,
      finalYes residual data nextProof → False) :
    StageNode (facts := facts)
      (family.FinalYesClosed nextYes nextNo finalYes finalNo) :=
  StageNode.usingStage
    (Required := family.YesDecision nextYes nextNo finalYes finalNo)
      fun state decision =>
        match decision with
        | .outerBypass data => .outerBypass data
        | .finalYes data nextProof proof =>
            (close state.residual data nextProof proof).elim
        | .finalNo data nextProof proof => .activeNo data nextProof proof
        | .nextNo data proof => .nextNo data proof
        | .initialNo data => .initialNo data

/-- Independently focus the final negative leaf.  All other leaves become an
opaque framework bypass, yielding the small reusable cursor used downstream. -/
noncomputable def StageNode.focusActiveCursorYesContinuationFinalNo
    (family : ActiveCursorYesContinuationFamily Residual)
    {nextYes nextNo : (residual : Residual) → family.ActiveData residual → Prop}
    {finalYes finalNo : (residual : Residual) →
      (data : family.ActiveData residual) → nextYes residual data → Prop}
    [Proofs.Contains
      (Available (family.YesDecision nextYes nextNo finalYes finalNo)) facts] :
    StageNode (facts := facts)
      (family.FinalNoActive nextYes nextNo finalYes finalNo) :=
  StageNode.usingStage
    (Required := family.YesDecision nextYes nextNo finalYes finalNo)
      fun _state decision =>
        match decision with
        | .outerBypass data => .bypass (.outerBypass data)
        | .finalYes data nextProof proof =>
            .bypass (.finalYes data nextProof proof)
        | .finalNo data nextProof proof => .active ⟨data, nextProof, proof⟩
        | .nextNo data proof => .bypass (.nextNo data proof)
        | .initialNo data => .bypass (.initialNo data)

/-- Decide a paper predicate on a populated focused-yes payload. -/
noncomputable def StageNode.decideFocusedYesContinuation
    (family : FocusedYesContinuationFamily Residual)
    {nextYes nextNo : (residual : Residual) → family.ActiveData residual → Prop}
    [Proofs.Contains (Available family.Source) facts]
    (decideYes : ∀ residual data, Decidable (nextYes residual data))
    (noOfNotYes : ∀ residual data, ¬nextYes residual data → nextNo residual data) :
    StageNode (facts := facts) (family.Decision nextYes nextNo) :=
  StageNode.usingStage (Required := family.Source) fun state source =>
    match source with
    | .bypass data => .bypass data
    | .activeYes data outerProof output =>
        let active : family.ActiveData state.residual := ⟨data, outerProof, output⟩
        match decideYes state.residual active with
        | .isTrue proof => .yesBranch active proof
        | .isFalse absent => .noBranch active (noOfNotYes state.residual active absent)
    | .noBranch data proof => .outerNo data proof

/-- Decide a second predicate only on the positive leaf. -/
noncomputable def StageNode.decideFocusedYesContinuationYes
    (family : FocusedYesContinuationFamily Residual)
    {nextYes nextNo : (residual : Residual) → family.ActiveData residual → Prop}
    {finalYes finalNo : (residual : Residual) →
      (data : family.ActiveData residual) → nextYes residual data → Prop}
    [Proofs.Contains (Available (family.Decision nextYes nextNo)) facts]
    (decideYes : ∀ residual data nextProof,
      Decidable (finalYes residual data nextProof))
    (noOfNotYes : ∀ residual data nextProof, ¬finalYes residual data nextProof →
      finalNo residual data nextProof) :
    StageNode (facts := facts) (family.YesDecision nextYes nextNo finalYes finalNo) :=
  StageNode.usingStage (Required := family.Decision nextYes nextNo) fun state decision =>
    match decision with
    | .bypass data => .bypass data
    | .yesBranch data nextProof =>
        match decideYes state.residual data nextProof with
        | .isTrue proof => .finalYes data nextProof proof
        | .isFalse absent => .finalNo data nextProof
            (noOfNotYes state.residual data nextProof absent)
    | .noBranch data proof => .nextNo data proof
    | .outerNo data proof => .outerNo data proof

/-- Mark the negative leaf terminal without changing or rebuilding it. -/
noncomputable def StageNode.markFocusedYesContinuationNoTerminal
    (family : FocusedYesContinuationFamily Residual)
    {nextYes nextNo : (residual : Residual) → family.ActiveData residual → Prop}
    [Proofs.Contains (Available (family.Decision nextYes nextNo)) facts] :
    StageNode (facts := facts) (family.NoTerminal nextYes nextNo) :=
  StageNode.usingStage (Required := family.Decision nextYes nextNo) fun _state decision =>
    match decision with
    | .bypass data => .bypass data
    | .yesBranch data proof => .activeYes data proof
    | .noBranch data proof => .terminalNo data proof
    | .outerNo data proof => .outerNo data proof

/-- Close only the final positive leaf. -/
noncomputable def StageNode.closeFocusedYesContinuationFinalYes
    (family : FocusedYesContinuationFamily Residual)
    {nextYes nextNo : (residual : Residual) → family.ActiveData residual → Prop}
    {finalYes finalNo : (residual : Residual) →
      (data : family.ActiveData residual) → nextYes residual data → Prop}
    [Proofs.Contains (Available
      (family.YesDecision nextYes nextNo finalYes finalNo)) facts]
    (close : ∀ residual data nextProof, finalYes residual data nextProof → False) :
    StageNode (facts := facts)
      (family.FinalYesClosed nextYes nextNo finalYes finalNo) :=
  StageNode.usingStage
    (Required := family.YesDecision nextYes nextNo finalYes finalNo) fun state decision =>
    match decision with
    | .bypass data => .bypass data
    | .finalYes data nextProof proof =>
        (close state.residual data nextProof proof).elim
    | .finalNo data nextProof proof => .activeNo data nextProof proof
    | .nextNo data proof => .nextNo data proof
    | .outerNo data proof => .outerNo data proof

/-- Focus the final negative leaf; Core owns every bypass constructor. -/
noncomputable def StageNode.focusFocusedYesContinuationFinalNo
    (family : FocusedYesContinuationFamily Residual)
    {nextYes nextNo : (residual : Residual) → family.ActiveData residual → Prop}
    {finalYes finalNo : (residual : Residual) →
      (data : family.ActiveData residual) → nextYes residual data → Prop}
    [Proofs.Contains (Available
      (family.YesDecision nextYes nextNo finalYes finalNo)) facts] :
    StageNode (facts := facts)
      (family.FinalNoActive nextYes nextNo finalYes finalNo) :=
  StageNode.usingStage
    (Required := family.YesDecision nextYes nextNo finalYes finalNo) fun _state decision =>
    match decision with
    | .bypass data => .bypass (.bypass data)
    | .finalYes data nextProof proof => .bypass (.finalYes data nextProof proof)
    | .finalNo data nextProof proof => .active ⟨data, nextProof, proof⟩
    | .nextNo data proof => .bypass (.nextNo data proof)
    | .outerNo data proof => .bypass (.outerNo data proof)

/-- Focus and exhaustively decide the active inner-no payload while preserving
the populated sibling and outer bypass as framework-owned data. -/
noncomputable def StageNode.decideDependentDecisionOnNoNoAfterYes
    {Previous : Residual → Type uInput}
    {outerYes outerNo : (residual : Residual) → Previous residual → Prop}
    {OuterNoOutput : (residual : Residual) → (previous : Previous residual) →
      outerNo residual previous → Type uTarget}
    {innerYes innerNo : (residual : Residual) →
      (previous : Previous residual) →
      (outerProof : outerNo residual previous) →
      OuterNoOutput residual previous outerProof → Prop}
    {YesOutput : (residual : Residual) → (previous : Previous residual) →
      (outerProof : outerNo residual previous) →
      (outerOutput : OuterNoOutput residual previous outerProof) →
      innerYes residual previous outerProof outerOutput → Type uStage}
    {Current : (residual : Residual) → (previous : Previous residual) →
      (outerProof : outerNo residual previous) →
      (outerOutput : OuterNoOutput residual previous outerProof) →
      innerNo residual previous outerProof outerOutput → Type uOccurrence}
    {yes no : (residual : Residual) →
      DependentDecisionOnNoNoAfterYesActive Previous outerNo OuterNoOutput
        innerNo Current residual → Prop}
    [Proofs.Contains
      (Available (DependentDecisionOnNoNoAfterYes Previous outerYes outerNo
        OuterNoOutput innerYes innerNo YesOutput Current)) facts]
    (decideYes : ∀ residual data, Decidable (yes residual data))
    (noOfNotYes : ∀ residual data, ¬ yes residual data → no residual data) :
    StageNode (facts := facts)
      (FocusedBranchDecision
        (DependentDecisionOnNoNoAfterYesBypass Previous outerYes outerNo
          OuterNoOutput innerYes YesOutput)
        (DependentDecisionOnNoNoAfterYesActive Previous outerNo OuterNoOutput
          innerNo Current) yes no) :=
  StageNode.usingStage
    (Required := DependentDecisionOnNoNoAfterYes Previous outerYes outerNo
      OuterNoOutput innerYes innerNo YesOutput Current) fun state source =>
      match source with
      | .outerYesBranch previous proof =>
          .bypass (.outerYesBranch previous proof)
      | .innerYesBranch previous outerProof outerOutput innerProof output =>
          .bypass (.innerYesBranch previous outerProof outerOutput innerProof output)
      | .innerNoBranch previous outerProof outerOutput innerProof current =>
          let data : DependentDecisionOnNoNoAfterYesActive Previous outerNo
              OuterNoOutput innerNo Current state.residual :=
            ⟨previous, outerProof, outerOutput, innerProof, current⟩
          match decideYes state.residual data with
          | .isTrue proof => .yesBranch data proof
          | .isFalse absent =>
              .noBranch data (noOfNotYes state.residual data absent)

/-- Exhaustively decide one predicate on a reusable focused cursor. -/
noncomputable def StageNode.decideFocusedBranch
    {Bypass : Residual → Type uInput}
    {Active : Residual → Type uTarget}
    {yes no : (residual : Residual) → Active residual → Prop}
    [Proofs.Contains (Available (FocusedBranch Bypass Active)) facts]
    (decideYes : ∀ residual data, Decidable (yes residual data))
    (noOfNotYes : ∀ residual data, ¬ yes residual data → no residual data) :
    StageNode (facts := facts) (FocusedBranchDecision Bypass Active yes no) :=
  StageNode.usingStage (Required := FocusedBranch Bypass Active)
    fun state cursor =>
      match cursor with
      | .bypass data => .bypass data
      | .active data =>
          match decideYes state.residual data with
          | .isTrue proof => .yesBranch data proof
          | .isFalse absent => .noBranch data (noOfNotYes state.residual data absent)

noncomputable def StageNode.closeFocusedBranchYes
    {Bypass : Residual → Type uInput}
    {Active : Residual → Type uTarget}
    {yes no : (residual : Residual) → Active residual → Prop}
    [Proofs.Contains
      (Available (FocusedBranchDecision Bypass Active yes no)) facts]
    (close : ∀ residual data, yes residual data → False) :
    StageNode (facts := facts)
      (FocusedBranchDecisionYesClosed Bypass Active yes no) :=
  StageNode.usingStage (Required := FocusedBranchDecision Bypass Active yes no)
    fun state decision =>
      match decision with
      | .bypass data => .bypass data
      | .yesBranch data proof => (close state.residual data proof).elim
      | .noBranch data proof => .activeNo data proof

/-- Close only the active no leaf of a focused no continuation.  The opaque
bypass and the already handled yes leaf are retained as terminal data. -/
noncomputable def StageNode.closeFocusedBranchNoContinuation
    {Bypass : Residual → Type uInput}
    {Active : Residual → Type uTarget}
    {yes no : (residual : Residual) → Active residual → Prop}
    {Output : (residual : Residual) → (data : Active residual) →
      no residual data → Type uStage}
    [Proofs.Contains
      (Available (FocusedBranchDecisionNoContinuation
        Bypass Active yes no Output)) facts]
    (close : ∀ residual data proof,
      Output residual data proof → False) :
    StageNode (facts := facts)
      (FocusedBranchDecisionNoClosed Bypass Active yes no) :=
  StageNode.usingStage
    (Required := FocusedBranchDecisionNoContinuation
      Bypass Active yes no Output) fun state continuation =>
      match continuation with
      | .bypass data => .bypass data
      | .yesBranch data proof => .activeYes data proof
      | .activeNo data proof output =>
          (close state.residual data proof output).elim

/-- Continue only the yes leaf of a focused decision.  The bypass and no leaf
are transported literally by Core. -/
noncomputable def StageNode.continueFocusedBranchYes
    {Bypass : Residual → Type uInput}
    {Active : Residual → Type uTarget}
    {yes no : (residual : Residual) → Active residual → Prop}
    {Output : (residual : Residual) → (data : Active residual) →
      yes residual data → Sort uStage}
    [Proofs.Contains
      (Available (FocusedBranchDecision Bypass Active yes no)) facts]
    (produce : ∀ residual data proof, Output residual data proof) :
    StageNode (facts := facts)
      (FocusedBranchDecisionYesContinuation Bypass Active yes no Output) :=
  StageNode.usingStage
    (Required := FocusedBranchDecision Bypass Active yes no)
      fun state decision =>
        match decision with
        | .bypass data => .bypass data
        | .yesBranch data proof =>
            .activeYes data proof (produce state.residual data proof)
        | .noBranch data proof => .noBranch data proof

/-- Replace the payload on the literal yes continuation of a focused
decision.  Core retains the predecessor continuation in the accumulated
ledger and transports both untouched leaves. -/
noncomputable def StageNode.mapFocusedBranchYesContinuation
    {Bypass : Residual → Type uInput}
    {Active : Residual → Type uTarget}
    {yes no : (residual : Residual) → Active residual → Prop}
    {Output : (residual : Residual) → (data : Active residual) →
      yes residual data → Sort uStage}
    {Next : (residual : Residual) → (data : Active residual) →
      yes residual data → Sort uOccurrence}
    [Proofs.Contains (Available
      (FocusedBranchDecisionYesContinuation Bypass Active yes no Output)) facts]
    (produce : ∀ residual data proof,
      Output residual data proof → Next residual data proof) :
    StageNode (facts := facts)
      (FocusedBranchDecisionYesContinuation Bypass Active yes no Next) :=
  StageNode.usingStage
    (Required := FocusedBranchDecisionYesContinuation Bypass Active yes no Output)
      fun state continuation =>
        match continuation with
        | .bypass data => .bypass data
        | .activeYes data proof output =>
            .activeYes data proof (produce state.residual data proof output)
        | .noBranch data proof => .noBranch data proof

/-- Close a focused yes leaf after it has already been continued with a
payload.  Core consumes the exact accumulated yes-continuation stage,
transports the bypass and untouched no sibling, and exposes the canonical
focused-yes-closed state.  The caller supplies only the mathematical
contradiction for the latest payload. -/
noncomputable def StageNode.closeFocusedBranchYesContinuation
    {Bypass : Residual → Type uInput}
    {Active : Residual → Type uTarget}
    {yes no : (residual : Residual) → Active residual → Prop}
    {Output : (residual : Residual) → (data : Active residual) →
      yes residual data → Sort uStage}
    [Proofs.Contains (Available
      (FocusedBranchDecisionYesContinuation Bypass Active yes no Output)) facts]
    (close : ∀ residual data proof,
      Output residual data proof → False) :
    StageNode (facts := facts)
      (FocusedBranchDecisionYesClosed Bypass Active yes no) :=
  StageNode.usingStage
    (Required := FocusedBranchDecisionYesContinuation
      Bypass Active yes no Output) fun state continuation =>
      match continuation with
      | .bypass data => .bypass data
      | .activeYes data proof output =>
          (close state.residual data proof output).elim
      | .noBranch data proof => .activeNo data proof

/-- Decide one paper-local predicate on the payload already attached to the
yes leaf.  The accumulated ledger supplies the predecessor continuation;
Core alone transports the bypass and untouched no sibling. -/
noncomputable def StageNode.decideFocusedBranchYesContinuation
    {Bypass : Residual → Type uInput}
    {Active : Residual → Type uTarget}
    {outerYes outerNo : (residual : Residual) → Active residual → Prop}
    {Output : (residual : Residual) → (data : Active residual) →
      outerYes residual data → Sort uStage}
    {innerYes innerNo : (residual : Residual) → (data : Active residual) →
      (outerProof : outerYes residual data) → Output residual data outerProof → Prop}
    [Proofs.Contains (Available
      (FocusedBranchDecisionYesContinuation Bypass Active outerYes outerNo Output)) facts]
    (decideYes : ∀ residual data outerProof output,
      Decidable (innerYes residual data outerProof output))
    (noOfNotYes : ∀ residual data outerProof output,
      ¬ innerYes residual data outerProof output →
        innerNo residual data outerProof output) :
    StageNode (facts := facts)
      (FocusedBranchYesContinuationDecision Bypass Active outerYes outerNo
        Output innerYes innerNo) :=
  StageNode.usingStage
    (Required := FocusedBranchDecisionYesContinuation
      Bypass Active outerYes outerNo Output) fun state continuation =>
      match continuation with
      | .bypass data => .bypass data
      | .activeYes data outerProof output =>
          match decideYes state.residual data outerProof output with
          | .isTrue innerProof =>
              .activeYesYes data outerProof output innerProof
          | .isFalse absent =>
              .activeYesNo data outerProof output
                (noOfNotYes state.residual data outerProof output absent)
      | .noBranch data proof => .noBranch data proof

/-- Mark only the inner-no leaf of a decision on a continued yes payload
terminal.  Core retains the terminal certificate and transports all sibling
constructors without an application callback. -/
noncomputable def StageNode.markFocusedBranchYesContinuationNoTerminal
    {Bypass : Residual → Type uInput}
    {Active : Residual → Type uTarget}
    {outerYes outerNo : (residual : Residual) → Active residual → Prop}
    {Output : (residual : Residual) → (data : Active residual) →
      outerYes residual data → Sort uStage}
    {innerYes innerNo : (residual : Residual) → (data : Active residual) →
      (outerProof : outerYes residual data) → Output residual data outerProof → Prop}
    [Proofs.Contains (Available
      (FocusedBranchYesContinuationDecision Bypass Active outerYes outerNo
        Output innerYes innerNo)) facts]
    : StageNode (facts := facts)
      (FocusedBranchYesContinuationNoTerminal Bypass Active outerYes outerNo
        Output innerYes innerNo) :=
  StageNode.usingStage
    (Required := FocusedBranchYesContinuationDecision Bypass Active outerYes
      outerNo Output innerYes innerNo) fun _state decision =>
      match decision with
      | .bypass data => .bypass data
      | .activeYesYes data outerProof output innerProof =>
          .activeYes data outerProof output innerProof
      | .activeYesNo data outerProof output innerProof =>
          .terminalNo data outerProof output innerProof
      | .noBranch data proof => .noBranch data proof

/-- Decide a second paper predicate only on the untouched no leaf after the
outer yes leaf has already advanced.  Core retains the outer successor and
the opaque bypass and constructs exactly the two complementary inner leaves. -/
noncomputable def StageNode.decideFocusedBranchYesContinuationNo
    {Bypass : Residual → Type uInput}
    {Active : Residual → Type uTarget}
    {outerYes outerNo : (residual : Residual) → Active residual → Prop}
    {OuterYesOutput : (residual : Residual) → (data : Active residual) →
      outerYes residual data → Sort uStage}
    {innerYes innerNo : (residual : Residual) →
      (data : Active residual) → outerNo residual data → Prop}
    [Proofs.Contains (Available
      (FocusedBranchDecisionYesContinuation Bypass Active outerYes outerNo
        OuterYesOutput)) facts]
    (decideYes : ∀ residual data outerProof,
      Decidable (innerYes residual data outerProof))
    (noOfNotYes : ∀ residual data outerProof,
      ¬ innerYes residual data outerProof →
        innerNo residual data outerProof) :
    StageNode (facts := facts)
      (FocusedBranchYesContinuationNoDecision Bypass Active outerYes outerNo
        OuterYesOutput innerYes innerNo) :=
  StageNode.usingStage
    (Required := FocusedBranchDecisionYesContinuation Bypass Active outerYes
      outerNo OuterYesOutput) fun state continuation =>
      match continuation with
      | .bypass data => .bypass data
      | .activeYes data proof output =>
          .outerYesBranch data proof output
      | .noBranch data outerProof =>
          match decideYes state.residual data outerProof with
          | .isTrue proof => .innerYesBranch data outerProof proof
          | .isFalse absent =>
              .innerNoBranch data outerProof
                (noOfNotYes state.residual data outerProof absent)

/-- Turn the already continued outer-yes leaf into terminal evidence, close
the inner-yes leaf, and expose only the literal inner-no leaf as the new
focused cursor.  No application callback transports any sibling branch. -/
noncomputable def StageNode.terminalizeFocusedBranchYesCloseNestedYes
    {Bypass : Residual → Type uInput}
    {Active : Residual → Type uTarget}
    {outerYes outerNo : (residual : Residual) → Active residual → Prop}
    {OuterYesOutput : (residual : Residual) → (data : Active residual) →
      outerYes residual data → Sort uStage}
    {innerYes innerNo : (residual : Residual) →
      (data : Active residual) → outerNo residual data → Prop}
    {Terminal : (residual : Residual) → (data : Active residual) →
      (proof : outerYes residual data) →
      OuterYesOutput residual data proof → Sort uOccurrence}
    [Proofs.Contains (Available
      (FocusedBranchYesContinuationNoDecision Bypass Active outerYes outerNo
        OuterYesOutput innerYes innerNo)) facts]
    (terminal : ∀ residual data proof output,
      Terminal residual data proof output)
    (close : ∀ residual data outerProof,
      innerYes residual data outerProof → False) :
    StageNode (facts := facts)
      (FocusedBranch
        (FocusedBranchYesTerminalBypass Bypass Active outerYes OuterYesOutput
          Terminal)
        (FocusedBranchNestedNoActive Active outerNo innerNo)) :=
  StageNode.usingStage
    (Required := FocusedBranchYesContinuationNoDecision Bypass Active outerYes
      outerNo OuterYesOutput innerYes innerNo) fun state decision =>
      match decision with
      | .bypass data => .bypass (.bypass data)
      | .outerYesBranch data proof output =>
          .bypass (.terminal data proof output
            (terminal state.residual data proof output))
      | .innerYesBranch data outerProof proof =>
          (close state.residual data outerProof proof).elim
      | .innerNoBranch data outerProof proof =>
          .active ⟨data, outerProof, proof⟩

/-- Append one node-local payload to the active constructor of a focused
branch.  Core owns the bypass transport and retains the exact active data. -/
noncomputable def StageNode.continueFocusedBranchActive
    {Bypass : Residual → Type uInput}
    {Active : Residual → Type uTarget}
    {Output : (residual : Residual) → Active residual → Type uStage}
    [Proofs.Contains (Available (FocusedBranch Bypass Active)) facts]
    (produce : ∀ residual data, Output residual data) :
    StageNode (facts := facts)
      (FocusedBranchActiveContinuation Bypass Active Output) :=
  StageNode.usingStage (Required := FocusedBranch Bypass Active)
    fun state branch =>
      match branch with
      | .bypass data => .bypass data
      | .active data => .active data (produce state.residual data)

noncomputable def StageNode.continueFocusedBranchNo
    {Bypass : Residual → Type uInput}
    {Active : Residual → Type uTarget}
    {yes no : (residual : Residual) → Active residual → Prop}
    {Output : (residual : Residual) → (data : Active residual) →
      no residual data → Sort uStage}
    [Proofs.Contains
      (Available (FocusedBranchDecision Bypass Active yes no)) facts]
    (produce : ∀ residual data proof, Output residual data proof) :
    StageNode (facts := facts)
      (FocusedBranchDecisionNoContinuation Bypass Active yes no Output) :=
  StageNode.usingStage (Required := FocusedBranchDecision Bypass Active yes no)
    fun state decision =>
      match decision with
      | .bypass data => .bypass data
      | .yesBranch data proof => .yesBranch data proof
      | .noBranch data proof => .activeNo data proof (produce state.residual data proof)

noncomputable def StageNode.mapFocusedBranchNoContinuation
    {Bypass : Residual → Type uInput}
    {Active : Residual → Type uTarget}
    {yes no : (residual : Residual) → Active residual → Prop}
    {Output : (residual : Residual) → (data : Active residual) →
      no residual data → Sort uStage}
    {Next : (residual : Residual) → (data : Active residual) →
      no residual data → Sort uOccurrence}
    [Proofs.Contains (Available
      (FocusedBranchDecisionNoContinuation Bypass Active yes no Output)) facts]
    (produce : ∀ residual data proof,
      Output residual data proof → Next residual data proof) :
    StageNode (facts := facts)
      (FocusedBranchDecisionNoContinuation Bypass Active yes no Next) :=
  StageNode.usingStage
    (Required := FocusedBranchDecisionNoContinuation Bypass Active yes no Output)
      fun state continuation =>
        match continuation with
        | .bypass data => .bypass data
        | .yesBranch data proof => .yesBranch data proof
        | .activeNo data proof output =>
            .activeNo data proof (produce state.residual data proof output)

/-- Continue the yes edge of an already continued dependent decision.  The
application supplies only the new mathematical producer; it cannot rebuild
the earlier decision, predecessor, branch proof, or current output. -/
noncomputable def StageNode.continueDependentDecisionYesAgain
    {Previous : Residual → Type uInput}
    {yes no : (residual : Residual) → Previous residual → Prop}
    {Current : (residual : Residual) → (previous : Previous residual) →
      yes residual previous → Type uTarget}
    {Next : (residual : Residual) → (previous : Previous residual) →
      (proof : yes residual previous) → Current residual previous proof →
        Type uStage}
    [Proofs.Contains
      (Available
        (DependentDecisionYesContinuation Previous yes no Current)) facts]
    (produce : (residual : Residual) → (previous : Previous residual) →
      (proof : yes residual previous) → (current : Current residual previous proof) →
        Next residual previous proof current) :
    StageNode (facts := facts)
      (DependentDecisionYesSuccessor Previous yes no Current Next) :=
  StageNode.usingStage
    (Required := DependentDecisionYesContinuation Previous yes no Current)
      fun state decision =>
        match decision with
        | .yesBranch previous proof current =>
            .yesBranch previous proof current
              (produce state.residual previous proof current)
        | .noBranch previous proof => .noBranch previous proof

/-- Replace the latest payload on the continued yes edge by a terminal
certificate derived from that payload. The preceding decision, its literal
yes proof, and the untouched no edge are transported by the framework; an
application supplies only the local closing implication. The consumed stage
remains in the accumulated ledger, so this operation does not discard its
mathematical output. -/
noncomputable def StageNode.closeDependentDecisionYesSuccessor
    {Previous : Residual → Type uInput}
    {yes no : (residual : Residual) → Previous residual → Prop}
    {Current : (residual : Residual) → (previous : Previous residual) →
      yes residual previous → Type uTarget}
    {Latest : (residual : Residual) → (previous : Previous residual) →
      (proof : yes residual previous) → Current residual previous proof →
        Type uStage}
    {Closed : (residual : Residual) → (previous : Previous residual) →
      (proof : yes residual previous) → Current residual previous proof →
        Type uOccurrence}
    [Proofs.Contains
      (Available
        (DependentDecisionYesSuccessor Previous yes no Current Latest)) facts]
    (close : (residual : Residual) → (previous : Previous residual) →
      (proof : yes residual previous) →
      (current : Current residual previous proof) →
      Latest residual previous proof current →
        Closed residual previous proof current) :
    StageNode (facts := facts)
      (DependentDecisionYesSuccessor Previous yes no Current Closed) :=
  StageNode.usingStage
    (Required := DependentDecisionYesSuccessor Previous yes no Current Latest)
      fun state decision =>
        match decision with
        | .yesBranch previous proof current latest =>
            .yesBranch previous proof current
              (close state.residual previous proof current latest)
        | .noBranch previous proof => .noBranch previous proof

/-- Continue the untouched no edge of an accumulated yes continuation.  This
is the framework-owned diamond completion used when the two constructors of
one manuscript decision have different successor nodes. -/
noncomputable def StageNode.continueDependentDecisionNoAfterYes
    {Previous : Residual → Type uInput}
    {yes no : (residual : Residual) → Previous residual → Prop}
    {YesOutput : (residual : Residual) → (previous : Previous residual) →
      yes residual previous → Type uTarget}
    {NoOutput : (residual : Residual) → (previous : Previous residual) →
      no residual previous → Type uStage}
    [Proofs.Contains
      (Available
        (DependentDecisionYesContinuation Previous yes no YesOutput)) facts]
    (produce : (residual : Residual) → (previous : Previous residual) →
      (proof : no residual previous) → NoOutput residual previous proof) :
    StageNode (facts := facts)
      (DependentDecisionNoAfterYes Previous yes no YesOutput NoOutput) :=
  StageNode.usingStage
    (Required := DependentDecisionYesContinuation Previous yes no YesOutput)
      fun state decision =>
        match decision with
        | .yesBranch previous proof output => .yesBranch previous proof output
        | .noBranch previous proof =>
            .noBranch previous proof (produce state.residual previous proof)

/-- Continue exactly the inner no leaf of a nested dependent decision.  All
other leaves and their literal proofs are transported by the framework. -/
noncomputable def StageNode.continueDependentNestedNo
    {Previous : Residual → Type uInput}
    {outerYes outerNo : (residual : Residual) → Previous residual → Prop}
    {OuterYesOutput : (residual : Residual) →
      (previous : Previous residual) → outerYes residual previous → Type uTarget}
    {innerYes innerNo : (residual : Residual) → Previous residual → Prop}
    {Next : (residual : Residual) → (previous : Previous residual) →
      outerNo residual previous → innerNo residual previous → Type uStage}
    [Proofs.Contains
      (Available (DependentDecisionNoAfterYes Previous outerYes outerNo
        OuterYesOutput (fun residual previous _outerProof =>
          DependentDecisionAt innerYes innerNo residual previous))) facts]
    (produce : (residual : Residual) → (previous : Previous residual) →
      (outerProof : outerNo residual previous) →
      (innerProof : innerNo residual previous) →
        Next residual previous outerProof innerProof) :
    StageNode (facts := facts)
      (DependentNestedNoContinuation Previous outerYes outerNo OuterYesOutput
        innerYes innerNo Next) :=
  StageNode.usingStage
    (Required := DependentDecisionNoAfterYes Previous outerYes outerNo
      OuterYesOutput (fun residual previous _outerProof =>
        DependentDecisionAt innerYes innerNo residual previous))
      fun state decision =>
        match decision with
        | .yesBranch previous proof output =>
            .outerYesBranch previous proof output
        | .noBranch previous outerProof innerDecision =>
            match innerDecision with
            | .yesBranch innerProof =>
                .innerYesBranch previous outerProof innerProof
            | .noBranch innerProof =>
                .innerNoBranch previous outerProof innerProof
                  (produce state.residual previous outerProof innerProof)

def StageNode.asNode {Stage : Residual → Sort uTarget}
    (node : StageNode (facts := facts) Stage) :
    Node (facts := facts) (Available Stage) where
  prove := fun state => ⟨node.produce state⟩

/-- Recover an available proof certificate by type.  This is noncomputable
only because accumulated proof data live under `Nonempty`; it performs no
finite search. -/
noncomputable def requireStage {Stage : Residual → Sort uTarget}
    (state : State Residual facts)
    [Proofs.Contains (Available Stage) facts] : Stage state.residual :=
  Classical.choice (state.require (property := Available Stage))

/-! ## Compositional typed ledger queries -/

/-- A typed, branch-local read from one accumulated residual ledger.  Queries
compose without changing the residual and cannot manufacture unavailable
facts.  Their result is temporary input to a node producer; it is never
copied into the node's accumulated output by the framework. -/
structure LedgerQuery (Result : Residual → Sort uTarget) where
  read : (state : State Residual facts) → Result state.residual

namespace LedgerQuery

/-- Query one proposition already present in the accumulated ledger. -/
def fact {property : Residual → Prop}
    [Proofs.Contains property facts] :
    LedgerQuery (facts := facts) property where
  read := fun state => state.require

/-- Query one data-bearing stage already present in the accumulated ledger. -/
noncomputable def stage {Stage : Residual → Sort uTarget}
    [Proofs.Contains (Available Stage) facts] :
    LedgerQuery (facts := facts) Stage where
  read := fun state => state.requireStage

/-- Transform the result of a query without reading the ledger again.  This
is the preferred way to assemble a problem-specific named input view. -/
def map {Input : Residual → Sort uInput}
    {Output : Residual → Sort uTarget}
    (query : LedgerQuery (facts := facts) Input)
    (transform : (residual : Residual) → Input residual → Output residual) :
    LedgerQuery (facts := facts) Output where
  read := fun state => transform state.residual (query.read state)

/-- Retrieve a proposition through a registered theorem projection from an
accumulated certificate stage. -/
noncomputable def entailedStage
    {Stage : Residual → Sort uInput}
    {property : Residual → Prop}
    [Proofs.Contains (Available Stage) facts]
    [StageEntails Stage property] :
    LedgerQuery (facts := facts) property :=
  (stage (facts := facts) (Stage := Stage)).map fun _residual certificate =>
    StageEntails.prove certificate

/-- Combine two arbitrary queries at the identical residual.  Repeated use
supports any finite number of dependencies; no arity-specific retrieval API
is required. -/
def and {Left : Residual → Sort uInput}
    {Right : Residual → Sort uTarget}
    (left : LedgerQuery (facts := facts) Left)
    (right : LedgerQuery (facts := facts) Right) :
    LedgerQuery (facts := facts) (fun residual =>
      PProd (Left residual) (Right residual)) where
  read := fun state => ⟨left.read state, right.read state⟩

/-- Append one accumulated proposition to an existing query. -/
def andFact {Input : Residual → Sort uInput}
    {property : Residual → Prop}
    (query : LedgerQuery (facts := facts) Input)
    [Proofs.Contains property facts] :
    LedgerQuery (facts := facts) (fun residual =>
      PProd (Input residual) (property residual)) :=
  query.and (fact (facts := facts) (property := property))

/-- Append one accumulated data stage to an existing query. -/
noncomputable def andStage {Input : Residual → Sort uInput}
    {Stage : Residual → Sort uTarget}
    (query : LedgerQuery (facts := facts) Input)
    [Proofs.Contains (Available Stage) facts] :
    LedgerQuery (facts := facts) (fun residual =>
      PProd (Input residual) (Stage residual)) :=
  query.and (stage (facts := facts) (Stage := Stage))

/-- Append one registered mathematical consequence of an accumulated stage
to a query. Repetition collects any finite family of earlier results from the
same residual without arity-specific retrieval plumbing. -/
noncomputable def andEntailedStage
    {Input : Residual → Sort uInput}
    {Stage : Residual → Sort uStage}
    {property : Residual → Prop}
    (query : LedgerQuery (facts := facts) Input)
    [Proofs.Contains (Available Stage) facts]
    [StageEntails Stage property] :
    LedgerQuery (facts := facts) (fun residual =>
      PProd (Input residual) (property residual)) :=
  query.and (entailedStage (facts := facts) (Stage := Stage)
    (property := property))

end LedgerQuery

/-- Derive one new node certificate from an arbitrary typed ledger query.
The query resolves every inherited dependency at one stable residual; the
producer is responsible only for the node's new mathematical statement. -/
def StageNode.derive
    {Input : Residual → Sort uInput}
    {Stage : Residual → Sort uTarget}
    (query : LedgerQuery (facts := facts) Input)
    (produce : (state : State Residual facts) →
      Input state.residual → Stage state.residual) :
    StageNode (facts := facts) Stage where
  produce := fun state => produce state (query.read state)

/-- Query-bearing version of
`terminalizeFocusedBranchYesCloseNestedYes`.  The additional input is read
once from the same accumulated ledger as the nested decision; Core still owns
all bypass transport, terminal packaging, and surviving-leaf selection. -/
noncomputable def StageNode.terminalizeFocusedBranchYesCloseNestedYesDerived
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
    {Input : Residual → Sort uNext}
    [Proofs.Contains (Available
      (FocusedBranchYesContinuationNoDecision Bypass Active outerYes outerNo
        OuterYesOutput innerYes innerNo)) facts]
    (query : LedgerQuery (facts := facts) Input)
    (terminal : ∀ residual, Input residual → ∀ data proof output,
      Terminal residual data proof output)
    (close : ∀ residual, Input residual → ∀ data outerProof,
      innerYes residual data outerProof → False) :
    StageNode (facts := facts)
      (FocusedBranch
        (FocusedBranchYesTerminalBypass Bypass Active outerYes OuterYesOutput
          Terminal)
        (FocusedBranchNestedNoActive Active outerNo innerNo)) :=
  StageNode.derive
    (query.andStage
      (Stage := FocusedBranchYesContinuationNoDecision Bypass Active
        outerYes outerNo OuterYesOutput innerYes innerNo))
    fun state inputAndDecision =>
      match inputAndDecision.snd with
      | .bypass data => .bypass (.bypass data)
      | .outerYesBranch data proof output =>
          .bypass (.terminal data proof output
            (terminal state.residual inputAndDecision.fst data proof output))
      | .innerYesBranch data outerProof proof =>
          (close state.residual inputAndDecision.fst data outerProof proof).elim
      | .innerNoBranch data outerProof proof =>
          .active ⟨data, outerProof, proof⟩

/-- Prove one proposition from an arbitrary typed ledger query. This is the
proposition-valued counterpart of `StageNode.derive`. -/
def Node.derive
    {Input : Residual → Sort uInput}
    {property : Residual → Prop}
    (query : LedgerQuery (facts := facts) Input)
    (prove : (state : State Residual facts) →
      Input state.residual → property state.residual) :
    Node (facts := facts) property where
  prove := fun state => prove state (query.read state)

/-- Replace the payload on the exact no leaf of an active-cursor continuation
while resolving any additional inherited input from the same accumulated
ledger.  Core appends the literal continuation to the query and transports
both bypass constructors unchanged. -/
noncomputable def StageNode.mapActiveCursorDecisionNoContinuationDerived
    {Previous : Residual → Type uInput}
    {outerYes outerNo : (residual : Residual) → Previous residual → Prop}
    {OuterNoOutput : (residual : Residual) → (previous : Previous residual) →
      outerNo residual previous → Type uTarget}
    {innerYes innerNo : (residual : Residual) →
      (previous : Previous residual) →
      (outerProof : outerNo residual previous) →
      OuterNoOutput residual previous outerProof → Prop}
    {Current : (residual : Residual) → (previous : Previous residual) →
      (outerProof : outerNo residual previous) →
      (outerOutput : OuterNoOutput residual previous outerProof) →
      innerNo residual previous outerProof outerOutput → Type uStage}
    {yes no : (residual : Residual) → (previous : Previous residual) →
      (outerProof : outerNo residual previous) →
      (outerOutput : OuterNoOutput residual previous outerProof) →
      (innerProof : innerNo residual previous outerProof outerOutput) →
      Current residual previous outerProof outerOutput innerProof → Prop}
    {Output Next : (residual : Residual) → (previous : Previous residual) →
      (outerProof : outerNo residual previous) →
      (outerOutput : OuterNoOutput residual previous outerProof) →
      (innerProof : innerNo residual previous outerProof outerOutput) →
      (current : Current residual previous outerProof outerOutput innerProof) →
      no residual previous outerProof outerOutput innerProof current →
        Type uOccurrence}
    {Input : Residual → Sort uNext}
    [Proofs.Contains (Available (ActiveCursorDecisionNoContinuation Previous
      outerYes outerNo OuterNoOutput innerYes innerNo Current yes no Output)) facts]
    (query : LedgerQuery (facts := facts) Input)
    (produce : (residual : Residual) → Input residual →
      (previous : Previous residual) →
      (outerProof : outerNo residual previous) →
      (outerOutput : OuterNoOutput residual previous outerProof) →
      (innerProof : innerNo residual previous outerProof outerOutput) →
      (current : Current residual previous outerProof outerOutput innerProof) →
      (proof : no residual previous outerProof outerOutput innerProof current) →
      Output residual previous outerProof outerOutput innerProof current proof →
        Next residual previous outerProof outerOutput innerProof current proof) :
    StageNode (facts := facts) (ActiveCursorDecisionNoContinuation Previous
      outerYes outerNo OuterNoOutput innerYes innerNo Current yes no Next) :=
  StageNode.derive
    (query.andStage
      (Stage := ActiveCursorDecisionNoContinuation Previous outerYes outerNo
        OuterNoOutput innerYes innerNo Current yes no Output))
    fun state inputAndContinuation =>
      match inputAndContinuation.snd with
      | .outerYesBranch previous proof => .outerYesBranch previous proof
      | .yesBranch previous outerProof outerOutput innerProof current proof =>
          .yesBranch previous outerProof outerOutput innerProof current proof
      | .noBranch previous outerProof outerOutput innerProof current proof output =>
          .noBranch previous outerProof outerOutput innerProof current proof
            (produce state.residual inputAndContinuation.fst previous outerProof
              outerOutput innerProof current proof output)

/-- Replace the payload on the exact yes leaf of a focused continuation while
resolving any additional inherited input from the same accumulated ledger.
Core appends the literal continuation to the query and transports its bypass
and no leaves unchanged; applications provide only the new branch-local
mathematics. -/
noncomputable def StageNode.mapFocusedBranchYesContinuationDerived
    {Bypass : Residual → Type uInput}
    {Active : Residual → Type uTarget}
    {yes no : (residual : Residual) → Active residual → Prop}
    {Output : (residual : Residual) → (data : Active residual) →
      yes residual data → Sort uStage}
    {Input : Residual → Sort uNext}
    {Next : (residual : Residual) → (data : Active residual) →
      yes residual data → Sort uOccurrence}
    [Proofs.Contains (Available
      (FocusedBranchDecisionYesContinuation Bypass Active yes no Output)) facts]
    (query : LedgerQuery (facts := facts) Input)
    (produce : (residual : Residual) → Input residual →
      (data : Active residual) → (proof : yes residual data) →
      Output residual data proof → Next residual data proof) :
    StageNode (facts := facts)
      (FocusedBranchDecisionYesContinuation Bypass Active yes no Next) :=
  StageNode.derive
    (query.andStage
      (Stage := FocusedBranchDecisionYesContinuation
        Bypass Active yes no Output))
    fun state inputAndContinuation =>
      match inputAndContinuation.snd with
      | .bypass data => .bypass data
      | .activeYes data proof output =>
          .activeYes data proof
            (produce state.residual inputAndContinuation.fst data proof output)
      | .noBranch data proof => .noBranch data proof

/-- Continue a dependent yes edge while resolving an arbitrary typed query
from the same accumulated ledger. The application receives no `State` and
cannot rebuild, replace, or reach around the residual. -/
noncomputable def StageNode.continueDependentDecisionYesAgainDerived
    {Previous : Residual → Type uInput}
    {yes no : (residual : Residual) → Previous residual → Prop}
    {Current : (residual : Residual) → (previous : Previous residual) →
      yes residual previous → Type uTarget}
    {Input : Residual → Sort uStage}
    {Next : (residual : Residual) → (previous : Previous residual) →
      (proof : yes residual previous) → Current residual previous proof →
        Type uOccurrence}
    [Proofs.Contains
      (Available
        (DependentDecisionYesContinuation Previous yes no Current)) facts]
    (query : LedgerQuery (facts := facts) Input)
    (produce : (residual : Residual) → Input residual →
      (previous : Previous residual) → (proof : yes residual previous) →
      (current : Current residual previous proof) →
        Next residual previous proof current) :
    StageNode (facts := facts)
      (DependentDecisionYesSuccessor Previous yes no Current Next) :=
  StageNode.derive
    (query.andStage
      (Stage := DependentDecisionYesContinuation Previous yes no Current))
    fun state inputAndDecision =>
      match inputAndDecision.snd with
      | .yesBranch previous proof current =>
          .yesBranch previous proof current
            (produce state.residual inputAndDecision.fst previous proof current)
      | .noBranch previous proof => .noBranch previous proof

/-- Build a data-bearing node from one accumulated proposition and one
accumulated certificate stage. Retrieval and `Nonempty` elimination are
framework-owned; the application supplies only the mathematical producer. -/
noncomputable def StageNode.usingFactAndStage
    {required : Residual → Prop}
    {Required : Residual → Sort uInput}
    {Stage : Residual → Sort uTarget}
    [Proofs.Contains required facts]
    [Proofs.Contains (Available Required) facts]
    (produce : (state : State Residual facts) →
      required state.residual → Required state.residual →
        Stage state.residual) :
    StageNode (facts := facts) Stage where
  produce := fun state => produce state
    (state.require (property := required))
    (state.requireStage (Stage := Required))

/-- Build a data-bearing node from one accumulated branch fact and one exact
dependent predecessor.  The framework retrieves both inputs, evaluates the
successor on the literal predecessor value, transports it to the predecessor
named by the incoming edge, and hands the transported mathematical output to
`finish`.  Application code therefore never eliminates predecessor equality
or invokes `ExactHandoff.mapDependent` itself. -/
noncomputable def StageNode.usingFactAndExactStage
    {required : Residual → Prop}
    {Previous : Residual → Sort uInput}
    {expected : (residual : Residual) → Previous residual}
    {Next : (residual : Residual) → required residual →
      Previous residual → Sort uTarget}
    {Stage : Residual → Sort uTarget}
    [Proofs.Contains required facts]
    [Proofs.Contains
      (Available (fun residual => ExactHandoff (expected residual))) facts]
    (produceNext : (residual : Residual) →
      (proof : required residual) → (previous : Previous residual) →
        Next residual proof previous)
    (finish : (residual : Residual) → (proof : required residual) →
      Next residual proof (expected residual) → Stage residual) :
    StageNode (facts := facts) Stage where
  produce := fun state =>
    let proof := state.require (property := required)
    let previous := state.requireStage
      (Stage := fun residual => ExactHandoff (expected residual))
    finish state.residual proof
      (previous.mapDependent (produceNext state.residual proof)).output

/-- Canonical dependent successor construction from an exact accumulated
stage. The framework retrieves the literal predecessor, runs the supplied
successor on it, and transports the result to the value named by the incoming
edge. When the application uses the produced expression itself as the next
canonical name, this is the entire node handoff. -/
noncomputable def StageNode.mapExactStage
    {Previous : Residual → Sort uInput}
    {expected : (residual : Residual) → Previous residual}
    {Next : (residual : Residual) → Previous residual → Sort uTarget}
    [Proofs.Contains
      (Available (fun residual => ExactHandoff (expected residual))) facts]
    (produceNext : (residual : Residual) →
      (previous : Previous residual) → Next residual previous) :
    StageNode (facts := facts)
      (fun residual => ExactHandoff
        (produceNext residual (expected residual))) where
  produce := fun state =>
    let previous := state.requireStage
      (Stage := fun residual => ExactHandoff (expected residual))
    previous.mapDependent (produceNext state.residual)

/-- Variant of `mapExactStage` for an application that has a separately named
canonical successor.  Only the final equality between the produced expression
and that name remains application-supplied. -/
noncomputable def StageNode.usingExactStage
    {Previous : Residual → Sort uInput}
    {expected : (residual : Residual) → Previous residual}
    {Next : (residual : Residual) → Previous residual → Sort uTarget}
    {nextExpected : (residual : Residual) →
      Next residual (expected residual)}
    [Proofs.Contains
      (Available (fun residual => ExactHandoff (expected residual))) facts]
    (produceNext : (residual : Residual) →
      (previous : Previous residual) → Next residual previous)
    (produceExpected : ∀ residual,
      produceNext residual (expected residual) = nextExpected residual) :
    StageNode (facts := facts)
      (fun residual => ExactHandoff (nextExpected residual)) :=
  let canonical := StageNode.mapExactStage (facts := facts)
    (expected := expected) produceNext
  { produce := fun state =>
      (canonical.produce state).castExpected
        (produceExpected state.residual) }

def Node.run {property : Residual → Prop}
    (node : Node (facts := facts) property) (state : State Residual facts) :
    State Residual (property :: facts) :=
  state.add property (node.prove state)

def StageNode.run {Stage : Residual → Sort uTarget}
    (node : StageNode (facts := facts) Stage)
    (state : State Residual facts) :
    State Residual (Available Stage :: facts) :=
  node.asNode.run state

@[simp] theorem Node.run_residual {property : Residual → Prop}
    (node : Node (facts := facts) property) (state : State Residual facts) :
    (node.run state).residual = state.residual :=
  rfl

theorem Node.run_latest {property : Residual → Prop}
    (node : Node (facts := facts) property) (state : State Residual facts) :
    (node.run state).latest = node.prove state :=
  rfl

/-- A manuscript dichotomy on the current residual.  Both outcomes retain the
identical carrier and complete incoming fact bundle; the node supplies only
the exhaustive mathematical disjunction. -/
structure DecisionNode (yes no : Residual → Prop) where
  yesDecidable : (state : State Residual facts) →
    Decidable (yes state.residual)
  no_of_not_yes : (state : State Residual facts) →
    ¬ yes state.residual → no state.residual

/-- Canonical decision between a predicate and its literal complement. -/
def DecisionNode.complement (property : Residual → Prop)
    (decideProperty : (state : State Residual facts) →
      Decidable (property state.residual)) :
    DecisionNode (facts := facts) property
      (fun residual => ¬property residual) where
  yesDecidable := decideProperty
  no_of_not_yes := fun _state absent => absent

/-- A refinement state kernel-certified to retain one named residual. -/
structure ExactState (expected : Residual)
    (branchFacts : List (Residual → Prop)) where
  state : State Residual branchFacts
  residualExact : state.residual = expected

namespace ExactState

variable {expected : Residual}
variable {branchFacts : List (Residual → Prop)}

def add (branch : ExactState expected branchFacts)
    (property : Residual → Prop)
    (proof : property branch.state.residual) :
    ExactState expected (property :: branchFacts) where
  state := branch.state.add property proof
  residualExact := branch.residualExact

def runNode {property : Residual → Prop}
    (branch : ExactState expected branchFacts)
    (node : Node (facts := branchFacts) property) :
    ExactState expected (property :: branchFacts) :=
  branch.add property (node.prove branch.state)

def runStage {Stage : Residual → Sort uTarget}
    (branch : ExactState expected branchFacts)
    (node : StageNode (facts := branchFacts) Stage) :
    ExactState expected (Available Stage :: branchFacts) :=
  branch.runNode node.asNode

def require {property : Residual → Prop}
    (branch : ExactState expected branchFacts)
    [Proofs.Contains property branchFacts] :
    property branch.state.residual :=
  branch.state.require

noncomputable def requireStage {Stage : Residual → Sort uTarget}
    (branch : ExactState expected branchFacts)
    [Proofs.Contains (Available Stage) branchFacts] :
    Stage branch.state.residual :=
  branch.state.requireStage

end ExactState

inductive DecisionResult (state : State Residual facts)
    (yes no : Residual → Prop) where
  | yesBranch : ExactState state.residual (yes :: facts) →
      DecisionResult state yes no
  | noBranch : ExactState state.residual (no :: facts) →
      DecisionResult state yes no

/-- A branch result whose two continuations may have accumulated different
fact schemas.  The incoming state remains an index, so composition cannot
silently switch to an unrelated residual. -/
inductive BranchResult (state : State Residual facts)
    (yesFacts noFacts : List (Residual → Prop)) where
  | yesBranch : ExactState state.residual yesFacts →
      BranchResult state yesFacts noFacts
  | noBranch : ExactState state.residual noFacts →
      BranchResult state yesFacts noFacts

namespace DecisionResult

variable {yes no : Residual → Prop}
variable {state : State Residual facts}

/-- Eliminate a decision without re-running or reconstructing it. -/
def fold {Output : Sort uTarget}
    (result : DecisionResult state yes no)
    (onYes : ExactState state.residual (yes :: facts) → Output)
    (onNo : ExactState state.residual (no :: facts) → Output) : Output :=
  match result with
  | .yesBranch branch => onYes branch
  | .noBranch branch => onNo branch

/-- Refine both existing manuscript branches while retaining their complete
incoming fact bundles. -/
def mapBranches
    {yesFacts noFacts : List (Residual → Prop)}
    (result : DecisionResult state yes no)
    (onYes : ExactState state.residual (yes :: facts) →
      ExactState state.residual yesFacts)
    (onNo : ExactState state.residual (no :: facts) →
      ExactState state.residual noFacts) :
    BranchResult state yesFacts noFacts :=
  result.fold
    (fun branch => .yesBranch (onYes branch))
    (fun branch => .noBranch (onNo branch))

/-- Add one theorem only on the yes edge of an existing decision. -/
def mapYes {property : Residual → Prop}
    (result : DecisionResult state yes no)
    (prove : (branch : ExactState state.residual (yes :: facts)) →
      property branch.state.residual) :
    BranchResult state (property :: yes :: facts) (no :: facts) :=
  result.mapBranches
    (fun branch => branch.add property (prove branch)) id

/-- Add one data-bearing stage only on the yes edge. -/
def mapYesStage {Stage : Residual → Sort uTarget}
    (result : DecisionResult state yes no)
    (node : State.StageNode (facts := yes :: facts) Stage) :
    BranchResult state (State.Available Stage :: yes :: facts) (no :: facts) :=
  result.mapBranches (fun branch => branch.runStage node) id

/-- Add one theorem only on the no edge of an existing decision. -/
def mapNo {property : Residual → Prop}
    (result : DecisionResult state yes no)
    (prove : (branch : ExactState state.residual (no :: facts)) →
      property branch.state.residual) :
    BranchResult state (yes :: facts) (property :: no :: facts) :=
  result.mapBranches id
    (fun branch => branch.add property (prove branch))

/-- Add one data-bearing stage only on the no edge. -/
def mapNoStage {Stage : Residual → Sort uTarget}
    (result : DecisionResult state yes no)
    (node : State.StageNode (facts := no :: facts) Stage) :
    BranchResult state (yes :: facts) (State.Available Stage :: no :: facts) :=
  result.mapBranches id (fun branch => branch.runStage node)

/-- Continue both existing decision edges with their respective data-bearing
nodes in one framework operation.  The branch schemas, retained residual,
and stage availability facts are composed automatically; applications name
only the two mathematical producers already present in the manuscript. -/
def mapStages {YesStage NoStage : Residual → Sort uTarget}
    (result : DecisionResult state yes no)
    (yesNode : State.StageNode (facts := yes :: facts) YesStage)
    (noNode : State.StageNode (facts := no :: facts) NoStage) :
    BranchResult state
      (State.Available YesStage :: yes :: facts)
      (State.Available NoStage :: no :: facts) :=
  result.mapBranches
    (fun branch => branch.runStage yesNode)
    (fun branch => branch.runStage noNode)

end DecisionResult

namespace BranchResult

variable {state : State Residual facts}
variable {yesFacts noFacts : List (Residual → Prop)}

/-- Compose already refined branches without rebuilding their provenance. -/
def mapBranches
    {nextYesFacts nextNoFacts : List (Residual → Prop)}
    (result : BranchResult state yesFacts noFacts)
    (onYes : ExactState state.residual yesFacts →
      ExactState state.residual nextYesFacts)
    (onNo : ExactState state.residual noFacts →
      ExactState state.residual nextNoFacts) :
    BranchResult state nextYesFacts nextNoFacts :=
  match result with
  | .yesBranch branch => .yesBranch (onYes branch)
  | .noBranch branch => .noBranch (onNo branch)

/-- Continue only the yes branch of an already composed result. -/
def mapYes {property : Residual → Prop}
    (result : BranchResult state yesFacts noFacts)
    (prove : (branch : ExactState state.residual yesFacts) →
      property branch.state.residual) :
    BranchResult state (property :: yesFacts) noFacts :=
  result.mapBranches
    (fun branch => branch.add property (prove branch)) id

/-- Continue the yes branch with one data-bearing proof stage. -/
def mapYesStage {Stage : Residual → Sort uTarget}
    (result : BranchResult state yesFacts noFacts)
    (node : State.StageNode (facts := yesFacts) Stage) :
    BranchResult state (State.Available Stage :: yesFacts) noFacts :=
  result.mapBranches (fun branch => branch.runStage node) id

/-- Continue only the no branch of an already composed result. -/
def mapNo {property : Residual → Prop}
    (result : BranchResult state yesFacts noFacts)
    (prove : (branch : ExactState state.residual noFacts) →
      property branch.state.residual) :
    BranchResult state yesFacts (property :: noFacts) :=
  result.mapBranches id
    (fun branch => branch.add property (prove branch))

/-- Continue the no branch with one data-bearing proof stage. -/
def mapNoStage {Stage : Residual → Sort uTarget}
    (result : BranchResult state yesFacts noFacts)
    (node : State.StageNode (facts := noFacts) Stage) :
    BranchResult state yesFacts (State.Available Stage :: noFacts) :=
  result.mapBranches id (fun branch => branch.runStage node)

end BranchResult

def DecisionNode.run {yes no : Residual → Prop}
    (node : DecisionNode (facts := facts) yes no)
    (state : State Residual facts) : DecisionResult state yes no :=
  match node.yesDecidable state with
  | .isTrue proof => .yesBranch ⟨state.add yes proof, rfl⟩
  | .isFalse proof =>
      .noBranch ⟨state.add no (node.no_of_not_yes state proof), rfl⟩

/-- Generic strict-or-equal decision under a proved upper bound. The
framework owns decidability, antisymmetry, and exhaustiveness. -/
def DecisionNode.ltOrEq {Value : Type uInput} [LinearOrder Value]
    (left right : Residual → Value)
    (upper : (state : State Residual facts) →
      left state.residual ≤ right state.residual) :
    DecisionNode (facts := facts)
      (fun residual => left residual < right residual)
      (fun residual => left residual = right residual) where
  yesDecidable := fun _state => inferInstance
  no_of_not_yes := fun state notStrict =>
    le_antisymm (upper state) (le_of_not_gt notStrict)

/-- Strict-or-equal decision whose upper bound is supplied by one accumulated
certificate stage. The application names only that stage and its local bound. -/
noncomputable def DecisionNode.ltOrEqUsingStage
    {Value : Type uInput} [LinearOrder Value]
    {Required : Residual → Sort uTarget}
    [Proofs.Contains (State.Available Required) facts]
    (left right : Residual → Value)
    (upper : (state : State Residual facts) → Required state.residual →
      left state.residual ≤ right state.residual) :
    DecisionNode (facts := facts)
      (fun residual => left residual < right residual)
      (fun residual => left residual = right residual) :=
  DecisionNode.ltOrEq left right fun state =>
    upper state (state.requireStage (Stage := Required))

/-- The only explicit work required when the manuscript really changes the
residual carrier: construct the target residual and transport the facts that
the target branch is allowed to consume. -/
structure Route (Target : Type uTarget)
    (targetFacts : List (Target → Prop)) where
  targetResidual : State Residual facts → Target
  targetProofs : (state : State Residual facts) →
    Proofs (targetResidual state) targetFacts

def route {Target : Type uTarget} {targetFacts : List (Target → Prop)}
    (state : State Residual facts)
    (adapter : Route (facts := facts) Target targetFacts) :
    State Target targetFacts where
  residual := adapter.targetResidual state
  proofs := adapter.targetProofs state

end State

/-- An occurrence-indexed family of current residual states. -/
structure Ledger (Residual : Type uResidual)
    (facts : List (Residual → Prop)) where
  residuals : FiniteResidualLedger.Ledger.{uOccurrence, uResidual} Residual
  proofs : ∀ occurrence, Proofs (residuals.event occurrence) facts

namespace Ledger

variable {Residual : Type uResidual}
variable {facts : List (Residual → Prop)}

noncomputable def initial
    (residuals : FiniteResidualLedger.Ledger.{uOccurrence, uResidual}
      Residual) : Ledger.{uOccurrence, uResidual} Residual [] where
  residuals := residuals
  proofs := fun _ => .nil

/-- A graph- or application-owned producer.  The framework maps it over the
exact input occurrence schedule and installs its first theorem as the first
accumulated fact. -/
structure Producer (Input : Type uInput) (property : Residual → Prop) where
  emit : Input → Residual
  prove : ∀ input, property (emit input)

/-- A producer whose emitted value or proof depends on the literal occurrence,
not merely on the input value stored there.  This is essential when duplicate
values have distinct provenance witnesses. -/
structure IndexedProducer {Input : Type uInput}
    (inputs : FiniteResidualLedger.Ledger.{uOccurrence, uInput} Input)
    (property : Residual → Prop) where
  emit : inputs.Occurrence → Residual
  prove : ∀ occurrence, property (emit occurrence)

/-- Start a refinement ledger from an occurrence-aware producer. Occurrence
identity and order are inherited definitionally from the input schedule. -/
noncomputable def produceIndexed {Input : Type uInput}
    {property : Residual → Prop}
    (inputs : FiniteResidualLedger.Ledger.{uOccurrence, uInput} Input)
    (producer : IndexedProducer (Residual := Residual) inputs property) :
    Ledger.{uOccurrence, uResidual} Residual [property] where
  residuals := {
    Occurrence := inputs.Occurrence
    occurrences := inputs.occurrences
    event := producer.emit }
  proofs := fun occurrence => .cons (producer.prove occurrence) .nil

@[simp] theorem produceIndexed_residual {Input : Type uInput}
    {property : Residual → Prop}
    (inputs : FiniteResidualLedger.Ledger.{uOccurrence, uInput} Input)
    (producer : IndexedProducer (Residual := Residual) inputs property)
    (occurrence : inputs.Occurrence) :
    (produceIndexed inputs producer).residuals.event occurrence =
      producer.emit occurrence :=
  rfl

/-- Install one occurrence-local theorem on an existing exact residual
schedule. This is the canonical provenance-seeding operation when the residual
carrier is already final and only its producer-origin proof is new. -/
noncomputable def certify
    (residuals : FiniteResidualLedger.Ledger.{uOccurrence, uResidual}
      Residual) {property : Residual → Prop}
    (prove : ∀ occurrence, property (residuals.event occurrence)) :
    Ledger.{uOccurrence, uResidual} Residual [property] :=
  produceIndexed residuals {
    emit := residuals.event
    prove := prove }

/-- Start a refinement ledger from an exact producer schedule.  This is the
initial `ledger.add(theorem)` operation: occurrence identity is inherited from
the input schedule and the producer supplies only its local theorem. -/
noncomputable def produce {Input : Type uInput}
    {property : Residual → Prop}
    (inputs : FiniteResidualLedger.Ledger.{uOccurrence, uInput} Input)
    (producer : Producer (Residual := Residual) Input property) :
    Ledger.{uOccurrence, uResidual} Residual [property] :=
  produceIndexed inputs {
    emit := fun occurrence => producer.emit (inputs.event occurrence)
    prove := fun occurrence => producer.prove (inputs.event occurrence) }

@[simp] theorem produce_residual {Input : Type uInput}
    {property : Residual → Prop}
    (inputs : FiniteResidualLedger.Ledger.{uOccurrence, uInput} Input)
    (producer : Producer (Residual := Residual) Input property)
    (occurrence : inputs.Occurrence) :
    (produce inputs producer).residuals.event occurrence =
      producer.emit (inputs.event occurrence) :=
  rfl

def state (ledger : Ledger.{uOccurrence, uResidual} Residual facts)
    (occurrence : ledger.residuals.Occurrence) : State Residual facts where
  residual := ledger.residuals.event occurrence
  proofs := ledger.proofs occurrence

/-- Type-directed occurrence-local fact access. -/
theorem require
    (ledger : Ledger.{uOccurrence, uResidual} Residual facts)
    {property : Residual → Prop} [Proofs.Contains property facts]
    (occurrence : ledger.residuals.Occurrence) :
    property (ledger.residuals.event occurrence) :=
  (ledger.state occurrence).require

/-- Retrieve accumulated data at one literal occurrence by its stage type. -/
noncomputable def requireStage {Stage : Residual → Sort uTarget}
    (ledger : Ledger.{uOccurrence, uResidual} Residual facts)
    [Proofs.Contains (State.Available Stage) facts]
    (occurrence : ledger.residuals.Occurrence) :
    Stage (ledger.residuals.event occurrence) :=
  (ledger.state occurrence).requireStage

/-- Add one occurrence-local theorem to the whole ledger.  This is the direct
Lean `ledger.add` surface: the caller proves only the new property from the
current occurrence state; the framework accumulates everything else. -/
noncomputable def add {property : Residual → Prop}
    (ledger : Ledger.{uOccurrence, uResidual} Residual facts)
    (prove : (occurrence : ledger.residuals.Occurrence) →
      property (ledger.state occurrence).residual) :
    Ledger.{uOccurrence, uResidual} Residual (property :: facts) where
  residuals := ledger.residuals
  proofs := fun occurrence =>
    .cons (prove occurrence) (ledger.proofs occurrence)

@[simp] theorem add_residuals {property : Residual → Prop}
    (ledger : Ledger.{uOccurrence, uResidual} Residual facts)
    (prove : (occurrence : ledger.residuals.Occurrence) →
      property (ledger.state occurrence).residual) :
    (ledger.add prove).residuals = ledger.residuals :=
  rfl

theorem add_latest {property : Residual → Prop}
    (ledger : Ledger.{uOccurrence, uResidual} Residual facts)
    (prove : (occurrence : ledger.residuals.Occurrence) →
      property (ledger.state occurrence).residual)
    (occurrence : ledger.residuals.Occurrence) :
    ((ledger.add prove).state occurrence).latest = prove occurrence :=
  rfl

/-- Run one proof node over every actual occurrence.  The finite universe,
event identity, and every earlier property are retained definitionally. -/
noncomputable def refine {property : Residual → Prop}
    (ledger : Ledger.{uOccurrence, uResidual} Residual facts)
    (node : State.Node (facts := facts) property) :
    Ledger.{uOccurrence, uResidual} Residual (property :: facts) where
  residuals := ledger.residuals
  proofs := fun occurrence =>
    .cons (node.prove (ledger.state occurrence)) (ledger.proofs occurrence)

@[simp] theorem refine_residuals {property : Residual → Prop}
    (ledger : Ledger.{uOccurrence, uResidual} Residual facts)
    (node : State.Node (facts := facts) property) :
    (ledger.refine node).residuals = ledger.residuals :=
  rfl

theorem refine_latest {property : Residual → Prop}
    (ledger : Ledger.{uOccurrence, uResidual} Residual facts)
    (node : State.Node (facts := facts) property)
    (occurrence : ledger.residuals.Occurrence) :
    ((ledger.refine node).state occurrence).latest =
      node.prove (ledger.state occurrence) :=
  rfl

/-- Run one data-bearing proof stage over every actual occurrence. -/
noncomputable def refineStage {Stage : Residual → Sort uTarget}
    (ledger : Ledger.{uOccurrence, uResidual} Residual facts)
    (node : State.StageNode (facts := facts) Stage) :
    Ledger.{uOccurrence, uResidual} Residual
      (State.Available Stage :: facts) :=
  ledger.refine node.asNode

@[simp] theorem refineStage_residuals {Stage : Residual → Sort uTarget}
    (ledger : Ledger.{uOccurrence, uResidual} Residual facts)
    (node : State.StageNode (facts := facts) Stage) :
    (ledger.refineStage node).residuals = ledger.residuals :=
  rfl

/-- Compose two branches already carrying the same accumulated fact schema.
The sum tag preserves literal occurrence identity, and no proof field is
reconstructed by application code. -/
noncomputable def append
    (left right : Ledger.{uOccurrence, uResidual} Residual facts) :
    Ledger.{uOccurrence, uResidual} Residual facts where
  residuals := left.residuals.append right.residuals
  proofs
    | .inl occurrence => left.proofs occurrence
    | .inr occurrence => right.proofs occurrence

/-- Restrict to an explicitly decidable family of existing occurrences while
retaining every accumulated fact. -/
noncomputable def restrict
    (ledger : Ledger.{uOccurrence, uResidual} Residual facts)
    (keep : ledger.residuals.Occurrence → Prop)
    (keepDecidable : ∀ occurrence, Decidable (keep occurrence)) :
    Ledger.{uOccurrence, uResidual} Residual facts where
  residuals := ledger.residuals.restrict keep keepDecidable
  proofs := fun occurrence => ledger.proofs occurrence.1

/-- The two occurrence ledgers produced by one manuscript decision.  Each
branch retains the original occurrence through an explicit projection, and
`coverage` certifies that no input occurrence is lost. -/
structure DecisionSplit (ledger : Ledger.{uOccurrence, uResidual} Residual facts)
    (yes no : Residual → Prop) where
  yesBranch : Ledger.{uOccurrence, uResidual} Residual (yes :: facts)
  noBranch : Ledger.{uOccurrence, uResidual} Residual (no :: facts)
  yesOriginal : yesBranch.residuals.Occurrence →
    ledger.residuals.Occurrence
  noOriginal : noBranch.residuals.Occurrence →
    ledger.residuals.Occurrence
  yesOriginal_injective : Function.Injective yesOriginal
  noOriginal_injective : Function.Injective noOriginal
  yesResidualExact : ∀ occurrence,
    yesBranch.residuals.event occurrence =
      ledger.residuals.event (yesOriginal occurrence)
  noResidualExact : ∀ occurrence,
    noBranch.residuals.event occurrence =
      ledger.residuals.event (noOriginal occurrence)
  disjoint : ∀ yesOccurrence noOccurrence,
    yesOriginal yesOccurrence ≠ noOriginal noOccurrence
  coverage : ∀ occurrence : ledger.residuals.Occurrence,
    (∃ branchOccurrence, yesOriginal branchOccurrence = occurrence) ∨
      (∃ branchOccurrence, noOriginal branchOccurrence = occurrence)

/-- Partition only the ledger's literal occurrence schedule through an
existing decision node.  No residual value is deduplicated and no ambient
state or graph universe is constructed. -/
noncomputable def decide {yes no : Residual → Prop}
    (ledger : Ledger.{uOccurrence, uResidual} Residual facts)
    (node : State.DecisionNode (facts := facts) yes no) :
    DecisionSplit ledger yes no := by
  let yesKeep : ledger.residuals.Occurrence → Prop := fun occurrence =>
    yes (ledger.state occurrence).residual
  let noKeep : ledger.residuals.Occurrence → Prop := fun occurrence =>
    ¬ yes (ledger.state occurrence).residual
  let yesDecidable : ∀ occurrence, Decidable (yesKeep occurrence) :=
    fun occurrence => node.yesDecidable (ledger.state occurrence)
  let noDecidable : ∀ occurrence, Decidable (noKeep occurrence) :=
    fun occurrence => by
      exact @instDecidableNot _ (node.yesDecidable (ledger.state occurrence))
  let yesRestricted := ledger.restrict yesKeep yesDecidable
  let noRestricted := ledger.restrict noKeep noDecidable
  let yesBranch := yesRestricted.add (property := yes) fun occurrence => by
    exact occurrence.property
  let noBranch := noRestricted.add (property := no) fun occurrence => by
    exact node.no_of_not_yes (ledger.state occurrence.1) occurrence.property
  refine {
    yesBranch := yesBranch
    noBranch := noBranch
    yesOriginal := fun occurrence => occurrence.1
    noOriginal := fun occurrence => occurrence.1
    yesOriginal_injective := fun _left _right equal => Subtype.ext equal
    noOriginal_injective := fun _left _right equal => Subtype.ext equal
    yesResidualExact := fun _occurrence => rfl
    noResidualExact := fun _occurrence => rfl
    disjoint := ?_
    coverage := ?_
  }
  · intro yesOccurrence noOccurrence same
    exact noOccurrence.property (by
      simpa [yesKeep, noKeep, same] using yesOccurrence.property)
  intro occurrence
  cases node.yesDecidable (ledger.state occurrence) with
  | isTrue proof =>
      exact Or.inl ⟨⟨occurrence, proof⟩, rfl⟩
  | isFalse proof =>
      exact Or.inr ⟨⟨occurrence, proof⟩, rfl⟩

/-- Every original occurrence has exactly one preimage in exactly one branch.
This is the reusable partition theorem consumed by downstream ledgers. -/
theorem DecisionSplit.uniqueCoverage {yes no : Residual → Prop}
    {ledger : Ledger.{uOccurrence, uResidual} Residual facts}
    (split : DecisionSplit ledger yes no)
    (occurrence : ledger.residuals.Occurrence) :
    (∃! branchOccurrence,
      split.yesOriginal branchOccurrence = occurrence) ∨
    (∃! branchOccurrence,
      split.noOriginal branchOccurrence = occurrence) := by
  rcases split.coverage occurrence with yesCovered | noCovered
  · rcases yesCovered with ⟨branchOccurrence, exactOriginal⟩
    exact Or.inl ⟨branchOccurrence, exactOriginal, fun other otherExact =>
      split.yesOriginal_injective (otherExact.trans exactOriginal.symm)⟩
  · rcases noCovered with ⟨branchOccurrence, exactOriginal⟩
    exact Or.inr ⟨branchOccurrence, exactOriginal, fun other otherExact =>
      split.noOriginal_injective (otherExact.trans exactOriginal.symm)⟩

/-- No input occurrence can be represented on both sides of the split. -/
theorem DecisionSplit.not_both {yes no : Residual → Prop}
    {ledger : Ledger.{uOccurrence, uResidual} Residual facts}
    (split : DecisionSplit ledger yes no)
    (yesOccurrence : split.yesBranch.residuals.Occurrence)
    (noOccurrence : split.noBranch.residuals.Occurrence) :
    split.yesOriginal yesOccurrence ≠ split.noOriginal noOccurrence :=
  split.disjoint yesOccurrence noOccurrence

/-- The tagged occurrence carrier of both exact decision branches. -/
abbrev DecisionSplit.BranchOccurrence {yes no : Residual → Prop}
    {ledger : Ledger.{uOccurrence, uResidual} Residual facts}
    (split : DecisionSplit ledger yes no) :=
  Sum split.yesBranch.residuals.Occurrence
    split.noBranch.residuals.Occurrence

/-- Forget a decision-branch tag while retaining the literal original
occurrence. -/
def DecisionSplit.original {yes no : Residual → Prop}
    {ledger : Ledger.{uOccurrence, uResidual} Residual facts}
    (split : DecisionSplit ledger yes no) :
    split.BranchOccurrence → ledger.residuals.Occurrence
  | .inl occurrence => split.yesOriginal occurrence
  | .inr occurrence => split.noOriginal occurrence

theorem DecisionSplit.original_injective {yes no : Residual → Prop}
    {ledger : Ledger.{uOccurrence, uResidual} Residual facts}
    (split : DecisionSplit ledger yes no) :
    Function.Injective split.original := by
  intro left right equal
  cases left with
  | inl left =>
      cases right with
      | inl right =>
          exact congrArg Sum.inl (split.yesOriginal_injective equal)
      | inr right =>
          exact False.elim (split.disjoint left right equal)
  | inr left =>
      cases right with
      | inl right =>
          exact False.elim (split.disjoint right left equal.symm)
      | inr right =>
          exact congrArg Sum.inr (split.noOriginal_injective equal)

theorem DecisionSplit.original_surjective {yes no : Residual → Prop}
    {ledger : Ledger.{uOccurrence, uResidual} Residual facts}
    (split : DecisionSplit ledger yes no) :
    Function.Surjective split.original := by
  intro occurrence
  rcases split.coverage occurrence with yesCovered | noCovered
  · rcases yesCovered with ⟨branchOccurrence, exactOriginal⟩
    exact ⟨.inl branchOccurrence, exactOriginal⟩
  · rcases noCovered with ⟨branchOccurrence, exactOriginal⟩
    exact ⟨.inr branchOccurrence, exactOriginal⟩

/-- A ledger decision is an exact partition of the original occurrence
schedule. The equivalence is proof-level and never enumerates another carrier. -/
noncomputable def DecisionSplit.occurrenceEquiv {yes no : Residual → Prop}
    {ledger : Ledger.{uOccurrence, uResidual} Residual facts}
    (split : DecisionSplit ledger yes no) :
    split.BranchOccurrence ≃ ledger.residuals.Occurrence :=
  Equiv.ofBijective split.original
    ⟨split.original_injective, split.original_surjective⟩

/-- Global uniqueness form of decision coverage: exactly one tagged branch
occurrence represents each original occurrence. -/
theorem DecisionSplit.globallyUniqueCoverage {yes no : Residual → Prop}
    {ledger : Ledger.{uOccurrence, uResidual} Residual facts}
    (split : DecisionSplit ledger yes no)
    (occurrence : ledger.residuals.Occurrence) :
    ∃! branchOccurrence : split.BranchOccurrence,
      split.original branchOccurrence = occurrence := by
  rcases split.original_surjective occurrence with
    ⟨branchOccurrence, exactOriginal⟩
  exact ⟨branchOccurrence, exactOriginal, fun other otherExact =>
    split.original_injective (otherExact.trans exactOriginal.symm)⟩

/-- Conservative executable envelope for materializing both restricted branch
enumerations: at most two predicate checks per literal input occurrence. -/
noncomputable def decideBudget
    (ledger : Ledger.{uOccurrence, uResidual} Residual facts) :
    PolynomialCheckBudget Unit where
  size := fun _ => ledger.residuals.checks
  checks := fun _ => 2 * ledger.residuals.checks
  coefficient := 2
  degree := 1
  bounded := by
    intro _unit
    simp
    omega

@[simp] theorem decideBudget_checks
    (ledger : Ledger.{uOccurrence, uResidual} Residual facts) :
    ledger.decideBudget.checks () = 2 * ledger.residuals.checks :=
  rfl

/-- Route every occurrence through one explicit carrier-changing adapter.
Occurrence identity and enumeration remain unchanged. -/
noncomputable def route {Target : Type uTarget}
    {targetFacts : List (Target → Prop)}
    (ledger : Ledger.{uOccurrence, uResidual} Residual facts)
    (adapter : State.Route (facts := facts) Target targetFacts) :
    Ledger.{uOccurrence, uTarget} Target targetFacts where
  residuals := {
    Occurrence := ledger.residuals.Occurrence
    occurrences := ledger.residuals.occurrences
    event := fun occurrence =>
      adapter.targetResidual (ledger.state occurrence) }
  proofs := by
    intro occurrence
    exact adapter.targetProofs (ledger.state occurrence)

end Ledger

end StructuralExhaustion.Core.ResidualRefinement
