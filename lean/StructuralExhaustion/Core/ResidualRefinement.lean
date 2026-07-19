import StructuralExhaustion.Core.FiniteResidualLedger
import StructuralExhaustion.Core.ExactHandoff
import StructuralExhaustion.Core.WorkBudget

namespace StructuralExhaustion.Core.ResidualRefinement

universe uOccurrence uResidual uTarget uInput uStage

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
