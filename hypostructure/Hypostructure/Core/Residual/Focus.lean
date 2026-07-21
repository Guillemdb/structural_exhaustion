import Hypostructure.Core.Residual.Decision

/-!
# Repeatable focused branch execution

A focus records which constructors of an accumulated stage remain live.  Each
focused node appends one conditional output to the literal predecessor: live
stages receive the new payload and inactive siblings receive no payload.  The
focus lifts through the extension, so the same API can be used for an
arbitrary number of downstream nodes without application-owned routing.

Active queries are proof-indexed reads.  They expose inherited values only on
the live branch and lift through every focused extension without copying those
values into a later output.
-/

namespace Hypostructure.Core.Residual.Focus

universe uPrevious uOutput uResult uOther

/-- Executable description of the live part of one accumulated stage. -/
structure Profile (Previous : Sort uPrevious) where
  Active : Previous -> Prop
  activeDecidable : (previous : Previous) -> Decidable (Active previous)

/-- One focused node output.  The inactive constructor carries only evidence
that this paper branch does not own the predecessor. -/
inductive Outcome {Previous : Sort uPrevious} (profile : Profile Previous)
    (Output : (previous : Previous) -> profile.Active previous -> Sort uOutput)
    (previous : Previous) where
  | active (proof : profile.Active previous)
      (output : Output previous proof) : Outcome profile Output previous
  | inactive (absent : Not (profile.Active previous)) :
      Outcome profile Output previous

/-- One focused execution is one extension of the literal predecessor. -/
abbrev Stage {Previous : Sort uPrevious} (profile : Profile Previous)
    (Output : (previous : Previous) -> profile.Active previous -> Sort uOutput) :=
  Ledger.Extension Previous (Outcome profile Output)

/-- Execute a local payload only on the focused branch.  Core performs the
branch decision and constructs both typed outcomes. -/
def run {Previous : Sort uPrevious} (profile : Profile Previous)
    {Output : (previous : Previous) -> profile.Active previous -> Sort uOutput}
    (previous : Previous)
    (onActive : (proof : profile.Active previous) -> Output previous proof) :
    Stage profile Output :=
  Ledger.extend previous <|
    match profile.activeDecidable previous with
    | .isTrue proof => .active proof (onActive proof)
    | .isFalse absent => .inactive absent

@[simp] theorem run_previous {Previous : Sort uPrevious}
    (profile : Profile Previous)
    {Output : (previous : Previous) -> profile.Active previous -> Sort uOutput}
    (previous : Previous)
    (onActive : (proof : profile.Active previous) -> Output previous proof) :
    (run profile previous onActive).previous = previous :=
  rfl

/-- The same branch remains focused after a node extends the ledger. -/
def successor {Previous : Sort uPrevious} (profile : Profile Previous)
    (Output : (previous : Previous) -> profile.Active previous -> Sort uOutput) :
    Profile (Stage profile Output) where
  Active := fun stage => profile.Active stage.previous
  activeDecidable := fun stage => profile.activeDecidable stage.previous

/-- A typed inherited read available only when the source lies on the focus. -/
structure ActiveQuery {Previous : Sort uPrevious} (profile : Profile Previous)
    (Result : (previous : Previous) -> profile.Active previous -> Sort uResult) where
  private mk ::
  read : (previous : Previous) -> (proof : profile.Active previous) ->
    Result previous proof

namespace ActiveQuery

/-- Read an ordinary accumulated-ledger query under any active branch proof. -/
def ofQuery {Previous : Sort uPrevious} {profile : Profile Previous}
    {Result : Previous -> Sort uResult} (query : Query Previous Result) :
    ActiveQuery profile fun previous _proof => Result previous :=
  .mk fun previous _proof => query.read previous

/-- Transform one active query without another ledger read. -/
def map {Previous : Sort uPrevious} {profile : Profile Previous}
    {Input : (previous : Previous) -> profile.Active previous -> Sort uResult}
    (query : ActiveQuery profile Input)
    {Output : (previous : Previous) -> profile.Active previous -> Sort uOutput}
    (transform : (previous : Previous) -> (proof : profile.Active previous) ->
      Input previous proof -> Output previous proof) :
    ActiveQuery profile Output :=
  .mk fun previous proof => transform previous proof (query.read previous proof)

@[simp] theorem read_map {Previous : Sort uPrevious}
    {profile : Profile Previous}
    {Input : (previous : Previous) -> profile.Active previous -> Sort uResult}
    (query : ActiveQuery profile Input)
    {Output : (previous : Previous) -> profile.Active previous -> Sort uOutput}
    (transform : (previous : Previous) -> (proof : profile.Active previous) ->
      Input previous proof -> Output previous proof)
    (previous : Previous) (proof : profile.Active previous) :
    (query.map transform).read previous proof =
      transform previous proof (query.read previous proof) :=
  rfl

/-- Read two active values from the identical predecessor and activity proof. -/
def and {Previous : Sort uPrevious} {profile : Profile Previous}
    {Left : (previous : Previous) -> profile.Active previous -> Sort uResult}
    {Right : (previous : Previous) -> profile.Active previous -> Sort uOther}
    (left : ActiveQuery profile Left) (right : ActiveQuery profile Right) :
    ActiveQuery profile fun previous proof =>
      PProd (Left previous proof) (Right previous proof) :=
  .mk fun previous proof =>
    ⟨left.read previous proof, right.read previous proof⟩

/-- Lift an inherited active query through one focused extension. -/
def preserve {Previous : Sort uPrevious} {profile : Profile Previous}
    {Result : (previous : Previous) -> profile.Active previous -> Sort uResult}
    (query : ActiveQuery profile Result)
    {Output : (previous : Previous) -> profile.Active previous -> Sort uOutput} :
    ActiveQuery (successor profile Output) fun stage proof =>
      Result stage.previous proof :=
  .mk fun stage proof => query.read stage.previous proof

@[simp] theorem read_preserve_at {Previous : Sort uPrevious}
    {profile : Profile Previous}
    {Result : (previous : Previous) -> profile.Active previous -> Sort uResult}
    (query : ActiveQuery profile Result)
    {Output : (previous : Previous) -> profile.Active previous -> Sort uOutput}
    (stage : Stage profile Output)
    (proof : (successor profile Output).Active stage) :
    (query.preserve (Output := Output)).read stage proof =
      query.read stage.previous proof :=
  rfl

/-- Read the value introduced by the latest focused extension.  Proof
irrelevance reconciles the branch witness stored by the framework with the
witness supplied by the downstream consumer. -/
def latest {Previous : Sort uPrevious} {profile : Profile Previous}
    {Output : (previous : Previous) -> profile.Active previous -> Sort uOutput} :
    ActiveQuery (successor profile Output) fun stage proof =>
      Output stage.previous proof :=
  .mk fun stage proof => by
    cases added : stage.added with
    | active stored output =>
        have equal : stored = proof := Subsingleton.elim _ _
        cases equal
        exact output
    | inactive absent =>
        exact (absent proof).elim

@[simp] theorem read_preserve {Previous : Sort uPrevious}
    {profile : Profile Previous}
    {Result : (previous : Previous) -> profile.Active previous -> Sort uResult}
    (query : ActiveQuery profile Result)
    {Output : (previous : Previous) -> profile.Active previous -> Sort uOutput}
    (previous : Previous) (proof : profile.Active previous)
    (output : Output previous proof) :
    (preserve query (Output := Output)).read
        (Ledger.extend previous (.active proof output)) proof =
      query.read previous proof :=
  rfl

end ActiveQuery

/-! ## Focuses generated by a Core binary decision -/

/-- Proof that a decision stage contains its exact yes constructor. -/
structure YesActive {Previous : Sort uPrevious} {Yes No : Previous -> Prop}
    (stage : Decision.Stage Yes No) : Prop where
  proof : Yes stage.previous
  selected : stage.added = .yesBranch proof

/-- The exact yes constructor of a binary decision remains live. -/
def yes {Previous : Sort uPrevious} {Yes No : Previous -> Prop} :
    Profile (Decision.Stage Yes No) where
  Active := YesActive
  activeDecidable := fun stage =>
    match selected : stage.added with
    | .yesBranch proof => .isTrue ⟨proof, selected⟩
    | .noBranch _proof =>
        .isFalse fun active => by
          have contradiction := selected.symm.trans active.selected
          cases contradiction

/-- Retrieve the yes proof selected by the focused decision constructor. -/
def yesProof {Previous : Sort uPrevious} {Yes No : Previous -> Prop} :
    ActiveQuery (yes (Yes := Yes) (No := No)) fun stage _active =>
      Yes stage.previous :=
  .mk fun _stage active => active.proof

/-- Proof that a decision stage contains its exact no constructor. -/
structure NoActive {Previous : Sort uPrevious} {Yes No : Previous -> Prop}
    (stage : Decision.Stage Yes No) : Prop where
  proof : No stage.previous
  selected : stage.added = .noBranch proof

/-- The exact no constructor of a binary decision remains live. -/
def no {Previous : Sort uPrevious} {Yes No : Previous -> Prop} :
    Profile (Decision.Stage Yes No) where
  Active := NoActive
  activeDecidable := fun stage =>
    match selected : stage.added with
    | .yesBranch _proof =>
        .isFalse fun active => by
          have contradiction := selected.symm.trans active.selected
          cases contradiction
    | .noBranch proof => .isTrue ⟨proof, selected⟩

/-- Retrieve the no proof selected by the focused decision constructor. -/
def noProof {Previous : Sort uPrevious} {Yes No : Previous -> Prop} :
    ActiveQuery (no (Yes := Yes) (No := No)) fun stage _active =>
      No stage.previous :=
  .mk fun _stage active => active.proof

end Hypostructure.Core.Residual.Focus
