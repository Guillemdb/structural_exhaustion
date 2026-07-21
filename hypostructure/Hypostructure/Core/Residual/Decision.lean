import Hypostructure.Core.Residual.Query

/-!
# Dependent binary residual decisions

A binary decision is indexed by its complete predecessor ledger.  Core chooses
the constructor from a decision procedure and a proof of the complementary
outcome.  Continuations are indexed by that exact decision stage, so advancing
one or both branches cannot change the predecessor or discard a sibling.
-/

namespace Hypostructure.Core.Residual.Decision

universe uPrevious uYesOutput uNoOutput uNextYesOutput uNextNoOutput

/-- The two exhaustive outcomes at one literal predecessor stage. -/
inductive Binary {Previous : Sort uPrevious}
    (Yes No : Previous -> Prop) (previous : Previous) where
  | yesBranch (proof : Yes previous) : Binary Yes No previous
  | noBranch (proof : No previous) : Binary Yes No previous

/-- The accumulated stage emitted by a binary decision. -/
abbrev Stage {Previous : Sort uPrevious}
    (Yes No : Previous -> Prop) :=
  Ledger.Extension Previous (Binary Yes No)

/-- Application-supplied mathematics for an exhaustive binary decision.
Applications supply decidability and the complementary theorem, not a branch
constructor. -/
structure Node (Previous : Sort uPrevious)
    (Yes No : Previous -> Prop) where
  private mk ::
  yesDecidable : (previous : Previous) -> Decidable (Yes previous)
  no_of_not_yes : (previous : Previous) -> Not (Yes previous) -> No previous

namespace Node

/-- Register a dependent exhaustive decision. -/
def create {Previous : Sort uPrevious} {Yes No : Previous -> Prop}
    (yesDecidable : (previous : Previous) -> Decidable (Yes previous))
    (no_of_not_yes : (previous : Previous) ->
      Not (Yes previous) -> No previous) :
    Node Previous Yes No :=
  .mk yesDecidable no_of_not_yes

/-- The canonical proposition-versus-complement decision. -/
def complement {Previous : Sort uPrevious} (Property : Previous -> Prop)
    (propertyDecidable : (previous : Previous) ->
      Decidable (Property previous)) :
    Node Previous Property (fun previous => Not (Property previous)) :=
  create propertyDecidable fun _previous absent => absent

/-- Execute the decision on its literal predecessor. -/
def run {Previous : Sort uPrevious} {Yes No : Previous -> Prop}
    (node : Node Previous Yes No) (previous : Previous) :
    Stage Yes No :=
  Ledger.extend previous <|
    match node.yesDecidable previous with
    | .isTrue proof => .yesBranch proof
    | .isFalse absent => .noBranch (node.no_of_not_yes previous absent)

@[simp] theorem run_previous
    {Previous : Sort uPrevious} {Yes No : Previous -> Prop}
    (node : Node Previous Yes No) (previous : Previous) :
    (node.run previous).previous = previous :=
  rfl

end Node

/-- A dependent continuation on both constructors of one exact binary
decision. -/
inductive Continuation {Previous : Sort uPrevious}
    {Yes No : Previous -> Prop}
    (YesOutput : (previous : Previous) -> Yes previous -> Sort uYesOutput)
    (NoOutput : (previous : Previous) -> No previous -> Sort uNoOutput)
    (previous : Previous) : Binary Yes No previous ->
      Type (max uYesOutput uNoOutput) where
  | yesBranch (proof : Yes previous) (output : YesOutput previous proof) :
      Continuation YesOutput NoOutput previous (.yesBranch proof)
  | noBranch (proof : No previous) (output : NoOutput previous proof) :
      Continuation YesOutput NoOutput previous (.noBranch proof)

/-- A stage that independently advances both constructors of a decision. -/
abbrev ContinuationStage {Previous : Sort uPrevious}
    {Yes No : Previous -> Prop}
    (YesOutput : (previous : Previous) -> Yes previous -> Sort uYesOutput)
    (NoOutput : (previous : Previous) -> No previous -> Sort uNoOutput) :=
  Ledger.Extension (Stage Yes No) fun decision =>
    Continuation YesOutput NoOutput decision.previous decision.added

/-- Advance both constructors independently while retaining the literal
decision stage as predecessor. -/
def advance {Previous : Sort uPrevious} {Yes No : Previous -> Prop}
    {YesOutput : (previous : Previous) -> Yes previous -> Sort uYesOutput}
    {NoOutput : (previous : Previous) -> No previous -> Sort uNoOutput}
    (decision : Stage Yes No)
    (onYes : (proof : Yes decision.previous) ->
      YesOutput decision.previous proof)
    (onNo : (proof : No decision.previous) ->
      NoOutput decision.previous proof) :
    ContinuationStage YesOutput NoOutput :=
  Ledger.extend decision <|
    match decision.added with
    | .yesBranch proof => .yesBranch proof (onYes proof)
    | .noBranch proof => .noBranch proof (onNo proof)

@[simp] theorem advance_previous
    {Previous : Sort uPrevious} {Yes No : Previous -> Prop}
    {YesOutput : (previous : Previous) -> Yes previous -> Sort uYesOutput}
    {NoOutput : (previous : Previous) -> No previous -> Sort uNoOutput}
    (decision : Stage Yes No)
    (onYes : (proof : Yes decision.previous) ->
      YesOutput decision.previous proof)
    (onNo : (proof : No decision.previous) ->
      NoOutput decision.previous proof) :
    (advance decision onYes onNo).previous = decision :=
  rfl

/-- Advance only the yes constructor.  The no constructor receives no new
mathematics and remains available literally in the predecessor decision. -/
abbrev YesContinuation {Previous : Sort uPrevious}
    {Yes No : Previous -> Prop}
    (YesOutput : (previous : Previous) -> Yes previous -> Sort uYesOutput) :=
  Continuation (Yes := Yes) (No := No) YesOutput
    (fun (previous : Previous) (_proof : No previous) => PUnit)

abbrev YesContinuationStage {Previous : Sort uPrevious}
    {Yes No : Previous -> Prop}
    (YesOutput : (previous : Previous) -> Yes previous -> Sort uYesOutput) :=
  ContinuationStage (Yes := Yes) (No := No) YesOutput
    (fun (previous : Previous) (_proof : No previous) => PUnit)

def continueYes {Previous : Sort uPrevious} {Yes No : Previous -> Prop}
    {YesOutput : (previous : Previous) -> Yes previous -> Sort uYesOutput}
    (decision : Stage Yes No)
    (onYes : (proof : Yes decision.previous) ->
      YesOutput decision.previous proof) :
    YesContinuationStage (Yes := Yes) (No := No) YesOutput :=
  advance decision onYes fun _proof => PUnit.unit

/-- Advance only the no constructor while retaining the yes sibling. -/
abbrev NoContinuation {Previous : Sort uPrevious}
    {Yes No : Previous -> Prop}
    (NoOutput : (previous : Previous) -> No previous -> Sort uNoOutput) :=
  Continuation (Yes := Yes) (No := No)
    (fun (previous : Previous) (_proof : Yes previous) => PUnit) NoOutput

abbrev NoContinuationStage {Previous : Sort uPrevious}
    {Yes No : Previous -> Prop}
    (NoOutput : (previous : Previous) -> No previous -> Sort uNoOutput) :=
  ContinuationStage (Yes := Yes) (No := No)
    (fun (previous : Previous) (_proof : Yes previous) => PUnit) NoOutput

def continueNo {Previous : Sort uPrevious} {Yes No : Previous -> Prop}
    {NoOutput : (previous : Previous) -> No previous -> Sort uNoOutput}
    (decision : Stage Yes No)
    (onNo : (proof : No decision.previous) ->
      NoOutput decision.previous proof) :
    NoContinuationStage (Yes := Yes) (No := No) NoOutput :=
  advance decision (fun _proof => PUnit.unit) onNo

/-! ## Successors of an already continued decision -/

/-- The next dependent payload on either arm of an already continued binary
decision.  The prior arm payload is an index, so it remains owned by the
literal predecessor ledger and is never copied into the new extension. -/
inductive ContinuationSuccessor {Previous : Sort uPrevious}
    {Yes No : Previous -> Prop}
    {CurrentYes : (previous : Previous) -> Yes previous -> Sort uYesOutput}
    {CurrentNo : (previous : Previous) -> No previous -> Sort uNoOutput}
    (NextYes : (previous : Previous) -> (proof : Yes previous) ->
      CurrentYes previous proof -> Sort uNextYesOutput)
    (NextNo : (previous : Previous) -> (proof : No previous) ->
      CurrentNo previous proof -> Sort uNextNoOutput)
    (previous : Previous) :
    {decision : Binary Yes No previous} ->
      Continuation CurrentYes CurrentNo previous decision ->
        Type (max (max uYesOutput uNoOutput)
          (max uNextYesOutput uNextNoOutput)) where
  | yesBranch (proof : Yes previous)
      (current : CurrentYes previous proof)
      (output : NextYes previous proof current) :
      ContinuationSuccessor NextYes NextNo previous
        (.yesBranch proof current)
  | noBranch (proof : No previous)
      (current : CurrentNo previous proof)
      (output : NextNo previous proof current) :
      ContinuationSuccessor NextYes NextNo previous
        (.noBranch proof current)

/-- Append one framework-owned successor on both arms of an already continued
decision while retaining that exact continuation as predecessor. -/
abbrev ContinuationSuccessorStage {Previous : Sort uPrevious}
    {Yes No : Previous -> Prop}
    {CurrentYes : (previous : Previous) -> Yes previous -> Sort uYesOutput}
    {CurrentNo : (previous : Previous) -> No previous -> Sort uNoOutput}
    (NextYes : (previous : Previous) -> (proof : Yes previous) ->
      CurrentYes previous proof -> Sort uNextYesOutput)
    (NextNo : (previous : Previous) -> (proof : No previous) ->
      CurrentNo previous proof -> Sort uNextNoOutput) :=
  Ledger.Extension (ContinuationStage CurrentYes CurrentNo) fun stage =>
    ContinuationSuccessor NextYes NextNo stage.previous.previous
      stage.added

/-- Construct the next payload from one exact current continuation.  Keeping
the decision index explicit lets dependent pattern matching refine each arm. -/
def Continuation.successor
    {Previous : Sort uPrevious} {Yes No : Previous -> Prop}
    {CurrentYes : (previous : Previous) -> Yes previous -> Sort uYesOutput}
    {CurrentNo : (previous : Previous) -> No previous -> Sort uNoOutput}
    {NextYes : (previous : Previous) -> (proof : Yes previous) ->
      CurrentYes previous proof -> Sort uNextYesOutput}
    {NextNo : (previous : Previous) -> (proof : No previous) ->
      CurrentNo previous proof -> Sort uNextNoOutput}
    {previous : Previous} {decision : Binary Yes No previous}
    (current : Continuation CurrentYes CurrentNo previous decision)
    (onYes : (proof : Yes previous) ->
      (output : CurrentYes previous proof) ->
        NextYes previous proof output)
    (onNo : (proof : No previous) ->
      (output : CurrentNo previous proof) ->
        NextNo previous proof output) :
    ContinuationSuccessor NextYes NextNo previous current :=
  match current with
  | .yesBranch proof output =>
      .yesBranch proof output (onYes proof output)
  | .noBranch proof output =>
      .noBranch proof output (onNo proof output)

/-- Advance both arms of an existing continuation.  Core performs the branch
inspection and constructs the indexed successor; callers provide only the
local computation for each arm. -/
def advanceContinuation {Previous : Sort uPrevious}
    {Yes No : Previous -> Prop}
    {CurrentYes : (previous : Previous) -> Yes previous -> Sort uYesOutput}
    {CurrentNo : (previous : Previous) -> No previous -> Sort uNoOutput}
    {NextYes : (previous : Previous) -> (proof : Yes previous) ->
      CurrentYes previous proof -> Sort uNextYesOutput}
    {NextNo : (previous : Previous) -> (proof : No previous) ->
      CurrentNo previous proof -> Sort uNextNoOutput}
    (stage : ContinuationStage CurrentYes CurrentNo)
    (onYes : (proof : Yes stage.previous.previous) ->
      (current : CurrentYes stage.previous.previous proof) ->
        NextYes stage.previous.previous proof current)
    (onNo : (proof : No stage.previous.previous) ->
      (current : CurrentNo stage.previous.previous proof) ->
        NextNo stage.previous.previous proof current) :
    ContinuationSuccessorStage NextYes NextNo :=
  Ledger.extend stage (stage.added.successor onYes onNo)

@[simp] theorem advanceContinuation_previous
    {Previous : Sort uPrevious} {Yes No : Previous -> Prop}
    {CurrentYes : (previous : Previous) -> Yes previous -> Sort uYesOutput}
    {CurrentNo : (previous : Previous) -> No previous -> Sort uNoOutput}
    {NextYes : (previous : Previous) -> (proof : Yes previous) ->
      CurrentYes previous proof -> Sort uNextYesOutput}
    {NextNo : (previous : Previous) -> (proof : No previous) ->
      CurrentNo previous proof -> Sort uNextNoOutput}
    (stage : ContinuationStage CurrentYes CurrentNo)
    (onYes : (proof : Yes stage.previous.previous) ->
      (current : CurrentYes stage.previous.previous proof) ->
        NextYes stage.previous.previous proof current)
    (onNo : (proof : No stage.previous.previous) ->
      (current : CurrentNo stage.previous.previous proof) ->
        NextNo stage.previous.previous proof current) :
    (advanceContinuation stage onYes onNo).previous = stage :=
  rfl

/-- Advance only the yes arm.  The no arm receives no mathematical payload;
its earlier data remains available in the exact predecessor. -/
abbrev YesContinuationSuccessorStage {Previous : Sort uPrevious}
    {Yes No : Previous -> Prop}
    {CurrentYes : (previous : Previous) -> Yes previous -> Sort uYesOutput}
    {CurrentNo : (previous : Previous) -> No previous -> Sort uNoOutput}
    (NextYes : (previous : Previous) -> (proof : Yes previous) ->
      CurrentYes previous proof -> Sort uNextYesOutput) :=
  ContinuationSuccessorStage NextYes
    (Yes := Yes) (No := No) (CurrentYes := CurrentYes)
    (CurrentNo := CurrentNo)
    (fun _previous _proof _current => PUnit.{0})

def continueYesBranch {Previous : Sort uPrevious}
    {Yes No : Previous -> Prop}
    {CurrentYes : (previous : Previous) -> Yes previous -> Sort uYesOutput}
    {CurrentNo : (previous : Previous) -> No previous -> Sort uNoOutput}
    {NextYes : (previous : Previous) -> (proof : Yes previous) ->
      CurrentYes previous proof -> Sort uNextYesOutput}
    (stage : ContinuationStage CurrentYes CurrentNo)
    (onYes : (proof : Yes stage.previous.previous) ->
      (current : CurrentYes stage.previous.previous proof) ->
        NextYes stage.previous.previous proof current) :
    YesContinuationSuccessorStage
      (Yes := Yes) (No := No) (CurrentYes := CurrentYes)
      (CurrentNo := CurrentNo) NextYes :=
  advanceContinuation stage onYes fun _proof _current => PUnit.unit

/-- Symmetric one-arm successor for a live no branch. -/
abbrev NoContinuationSuccessorStage {Previous : Sort uPrevious}
    {Yes No : Previous -> Prop}
    {CurrentYes : (previous : Previous) -> Yes previous -> Sort uYesOutput}
    {CurrentNo : (previous : Previous) -> No previous -> Sort uNoOutput}
    (NextNo : (previous : Previous) -> (proof : No previous) ->
      CurrentNo previous proof -> Sort uNextNoOutput) :=
  ContinuationSuccessorStage
    (Yes := Yes) (No := No) (CurrentYes := CurrentYes)
    (CurrentNo := CurrentNo)
    (fun _previous _proof _current => PUnit.{0}) NextNo

def continueNoBranch {Previous : Sort uPrevious}
    {Yes No : Previous -> Prop}
    {CurrentYes : (previous : Previous) -> Yes previous -> Sort uYesOutput}
    {CurrentNo : (previous : Previous) -> No previous -> Sort uNoOutput}
    {NextNo : (previous : Previous) -> (proof : No previous) ->
      CurrentNo previous proof -> Sort uNextNoOutput}
    (stage : ContinuationStage CurrentYes CurrentNo)
    (onNo : (proof : No stage.previous.previous) ->
      (current : CurrentNo stage.previous.previous proof) ->
        NextNo stage.previous.previous proof current) :
    NoContinuationSuccessorStage
      (Yes := Yes) (No := No) (CurrentYes := CurrentYes)
      (CurrentNo := CurrentNo) NextNo :=
  advanceContinuation stage (fun _proof _current => PUnit.unit) onNo

/-- The surviving no continuation after the yes constructor has been closed
by contradiction.  Its index forces it to describe the exact no constructor
of the predecessor decision. -/
inductive YesClosedNoContinuation {Previous : Sort uPrevious}
    {Yes No : Previous -> Prop}
    (NoOutput : (previous : Previous) -> No previous -> Sort uNoOutput)
    (previous : Previous) : Binary Yes No previous -> Type uNoOutput where
  | noBranch (proof : No previous) (output : NoOutput previous proof) :
      YesClosedNoContinuation NoOutput previous (.noBranch proof)

abbrev YesClosedNoStage {Previous : Sort uPrevious}
    {Yes No : Previous -> Prop}
    (NoOutput : (previous : Previous) -> No previous -> Sort uNoOutput) :=
  Ledger.Extension (Stage Yes No) fun decision =>
    YesClosedNoContinuation (Yes := Yes) (No := No) NoOutput
      decision.previous decision.added

/-- Close the yes constructor and continue only the exact no constructor. -/
def closeYesAndContinueNo
    {Previous : Sort uPrevious} {Yes No : Previous -> Prop}
    {NoOutput : (previous : Previous) -> No previous -> Sort uNoOutput}
    (decision : Stage Yes No)
    (closeYes : Yes decision.previous -> False)
    (onNo : (proof : No decision.previous) ->
      NoOutput decision.previous proof) :
    YesClosedNoStage (Yes := Yes) (No := No) NoOutput :=
  Ledger.extend decision <|
    match decision.added with
    | .yesBranch proof => (closeYes proof).elim
    | .noBranch proof => .noBranch proof (onNo proof)

/-- The surviving yes continuation after the no constructor has been closed
by contradiction. -/
inductive NoClosedYesContinuation {Previous : Sort uPrevious}
    {Yes No : Previous -> Prop}
    (YesOutput : (previous : Previous) -> Yes previous -> Sort uYesOutput)
    (previous : Previous) : Binary Yes No previous -> Type uYesOutput where
  | yesBranch (proof : Yes previous) (output : YesOutput previous proof) :
      NoClosedYesContinuation YesOutput previous (.yesBranch proof)

abbrev NoClosedYesStage {Previous : Sort uPrevious}
    {Yes No : Previous -> Prop}
    (YesOutput : (previous : Previous) -> Yes previous -> Sort uYesOutput) :=
  Ledger.Extension (Stage Yes No) fun decision =>
    NoClosedYesContinuation (Yes := Yes) (No := No) YesOutput
      decision.previous decision.added

/-- Close the no constructor and continue only the exact yes constructor. -/
def closeNoAndContinueYes
    {Previous : Sort uPrevious} {Yes No : Previous -> Prop}
    {YesOutput : (previous : Previous) -> Yes previous -> Sort uYesOutput}
    (decision : Stage Yes No)
    (closeNo : No decision.previous -> False)
    (onYes : (proof : Yes decision.previous) ->
      YesOutput decision.previous proof) :
    NoClosedYesStage (Yes := Yes) (No := No) YesOutput :=
  Ledger.extend decision <|
    match decision.added with
    | .yesBranch proof => .yesBranch proof (onYes proof)
    | .noBranch proof => (closeNo proof).elim

end Hypostructure.Core.Residual.Decision
