import Hypostructure.Core.Budget.Work
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

/-- Executable description of the live part of one accumulated stage.  The
branch selector is counted and carries its own polynomial envelope, so a
downstream executor cannot claim zero work while silently running an
unaccounted decision procedure. -/
structure Profile (Previous : Sort uPrevious) where
  private mk ::
  Active : Previous -> Prop
  select : (previous : Previous) -> Counted (Decidable (Active previous))
  selectionBudget : PolynomialCheckBudget Previous
  select_checks : forall previous,
    (select previous).checks = selectionBudget.checks previous

namespace Profile

/-- The proposition decider carried by a counted focus. -/
def activeDecidable {Previous : Sort uPrevious} (profile : Profile Previous)
    (previous : Previous) : Decidable (profile.Active previous) :=
  (profile.select previous).value

end Profile

/-- A proof-only focus that owns every predecessor. It performs no branch
inspection and is the only public constructor for a focus not inherited from
a framework decision. -/
def always (Previous : Sort uPrevious) : Profile Previous where
  Active := fun _previous => True
  select := fun _previous => Counted.pure (.isTrue trivial)
  selectionBudget := PolynomialCheckBudget.proofOnly Previous
  select_checks := fun _previous => rfl

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

/-- Execute one counted selector and, only on the active branch, one counted
payload. The callback receives the selector's exact count so it can retain
that evidence in its output. Core owns the sequential composition and records
the sum of selector and payload checks. -/
def runCountedPayload {Previous : Sort uPrevious} (profile : Profile Previous)
    (payloadBudget : PolynomialCheckBudget Previous)
    {Output : (previous : Previous) -> profile.Active previous -> Sort uOutput}
    (previous : Previous)
    (onActive : (proof : profile.Active previous) ->
      (selectionChecks : Nat) ->
      selectionChecks = profile.selectionBudget.checks previous ->
        Counted (Output previous proof))
    (_onActive_checks : forall proof selectionChecks exact,
      (onActive proof selectionChecks exact).checks =
        payloadBudget.checks previous) :
    Counted (Stage profile Output) :=
  let selection := profile.select previous
  let outcome : Counted (Outcome profile Output previous) :=
    match selection.value with
    | .isTrue proof =>
        let payload :=
          onActive proof selection.checks (profile.select_checks previous)
        { value := .active proof payload.value
          checks := selection.checks + payload.checks }
    | .isFalse absent =>
        { value := .inactive absent
          checks := selection.checks }
  { value := Ledger.extend previous outcome.value
    checks := outcome.checks }

@[simp] theorem runCountedPayload_previous {Previous : Sort uPrevious}
    (profile : Profile Previous)
    (payloadBudget : PolynomialCheckBudget Previous)
    {Output : (previous : Previous) -> profile.Active previous -> Sort uOutput}
    (previous : Previous)
    (onActive : (proof : profile.Active previous) ->
      (selectionChecks : Nat) ->
      selectionChecks = profile.selectionBudget.checks previous ->
        Counted (Output previous proof))
    (onActive_checks : forall proof selectionChecks exact,
      (onActive proof selectionChecks exact).checks =
        payloadBudget.checks previous) :
    (runCountedPayload profile payloadBudget previous onActive
      onActive_checks).value.previous = previous := by
  unfold runCountedPayload
  cases selected : (profile.select previous).value <;>
    simp [selected]

/-- On an active predecessor, exact work is the selector work plus the active
payload work, namely the exact schedule computed by budget composition. -/
theorem runCountedPayload_checks_of_active {Previous : Sort uPrevious}
    (profile : Profile Previous)
    (payloadBudget : PolynomialCheckBudget Previous)
    {Output : (previous : Previous) -> profile.Active previous -> Sort uOutput}
    (previous : Previous)
    (onActive : (proof : profile.Active previous) ->
      (selectionChecks : Nat) ->
      selectionChecks = profile.selectionBudget.checks previous ->
        Counted (Output previous proof))
    (onActive_checks : forall proof selectionChecks exact,
      (onActive proof selectionChecks exact).checks =
        payloadBudget.checks previous)
    (active : profile.Active previous) :
    (runCountedPayload profile payloadBudget previous onActive
      onActive_checks).checks =
      (profile.selectionBudget.add payloadBudget).checks previous := by
  cases selected : (profile.select previous).value with
  | isTrue proof =>
      simp only [runCountedPayload, selected]
      rw [onActive_checks, profile.select_checks]
      rfl
  | isFalse absent =>
      exact (absent active).elim

/-- On an inactive predecessor, the active callback is not run and exact work
is only the selector work. -/
theorem runCountedPayload_checks_of_inactive {Previous : Sort uPrevious}
    (profile : Profile Previous)
    (payloadBudget : PolynomialCheckBudget Previous)
    {Output : (previous : Previous) -> profile.Active previous -> Sort uOutput}
    (previous : Previous)
    (onActive : (proof : profile.Active previous) ->
      (selectionChecks : Nat) ->
      selectionChecks = profile.selectionBudget.checks previous ->
        Counted (Output previous proof))
    (onActive_checks : forall proof selectionChecks exact,
      (onActive proof selectionChecks exact).checks =
        payloadBudget.checks previous)
    (inactive : Not (profile.Active previous)) :
    (runCountedPayload profile payloadBudget previous onActive
      onActive_checks).checks = profile.selectionBudget.checks previous := by
  cases selected : (profile.select previous).value with
  | isTrue proof => exact (inactive proof).elim
  | isFalse _absent =>
      simp only [runCountedPayload, selected]
      exact profile.select_checks previous

/-- Every outcome is bounded by the composed selector-plus-payload polynomial
envelope. The inactive branch pays less because it skips the payload. -/
theorem runCountedPayload_checks_bounded {Previous : Sort uPrevious}
    (profile : Profile Previous)
    (payloadBudget : PolynomialCheckBudget Previous)
    {Output : (previous : Previous) -> profile.Active previous -> Sort uOutput}
    (previous : Previous)
    (onActive : (proof : profile.Active previous) ->
      (selectionChecks : Nat) ->
      selectionChecks = profile.selectionBudget.checks previous ->
        Counted (Output previous proof))
    (onActive_checks : forall proof selectionChecks exact,
      (onActive proof selectionChecks exact).checks =
        payloadBudget.checks previous) :
    (runCountedPayload profile payloadBudget previous onActive
      onActive_checks).checks <=
      (profile.selectionBudget.add payloadBudget).coefficient *
        ((profile.selectionBudget.add payloadBudget).size previous + 1) ^
          (profile.selectionBudget.add payloadBudget).degree := by
  by_cases active : profile.Active previous
  · rw [runCountedPayload_checks_of_active profile payloadBudget previous
      onActive onActive_checks active]
    exact (profile.selectionBudget.add payloadBudget).bounded previous
  · rw [runCountedPayload_checks_of_inactive profile payloadBudget previous
      onActive onActive_checks active]
    exact Nat.le_trans
      (Nat.le_add_right
        (profile.selectionBudget.checks previous)
        (payloadBudget.checks previous))
      ((profile.selectionBudget.add payloadBudget).bounded previous)

/-- Execute one counted selector exactly once, use its value for routing, and
return that same execution's check count. The active payload receives the
exact count and its equality to the registered budget. This is the
zero-local-work specialization of `runCountedPayload`. -/
def runCounted {Previous : Sort uPrevious} (profile : Profile Previous)
    {Output : (previous : Previous) -> profile.Active previous -> Sort uOutput}
    (previous : Previous)
    (onActive : (proof : profile.Active previous) ->
      (checks : Nat) -> checks = profile.selectionBudget.checks previous ->
        Output previous proof) :
    Counted (Stage profile Output) :=
  runCountedPayload profile (PolynomialCheckBudget.proofOnly Previous) previous
    (fun proof checks exact => Counted.pure (onActive proof checks exact))
    (fun _proof _checks _exact => rfl)

@[simp] theorem runCounted_previous {Previous : Sort uPrevious}
    (profile : Profile Previous)
    {Output : (previous : Previous) -> profile.Active previous -> Sort uOutput}
    (previous : Previous)
    (onActive : (proof : profile.Active previous) ->
      (checks : Nat) -> checks = profile.selectionBudget.checks previous ->
        Output previous proof) :
    (runCounted profile previous onActive).value.previous = previous := by
  simp [runCounted]

@[simp] theorem runCounted_checks {Previous : Sort uPrevious}
    (profile : Profile Previous)
    {Output : (previous : Previous) -> profile.Active previous -> Sort uOutput}
    (previous : Previous)
    (onActive : (proof : profile.Active previous) ->
      (checks : Nat) -> checks = profile.selectionBudget.checks previous ->
        Output previous proof) :
    (runCounted profile previous onActive).checks =
      profile.selectionBudget.checks previous :=
  by
    by_cases active : profile.Active previous
    · simpa [runCounted, PolynomialCheckBudget.add,
        PolynomialCheckBudget.proofOnly, PolynomialCheckBudget.zero] using
        runCountedPayload_checks_of_active profile
          (PolynomialCheckBudget.proofOnly Previous) previous
          (fun proof checks exact => Counted.pure (onActive proof checks exact))
          (fun _proof _checks _exact => rfl) active
    · exact
        runCountedPayload_checks_of_inactive profile
          (PolynomialCheckBudget.proofOnly Previous) previous
          (fun proof checks exact => Counted.pure (onActive proof checks exact))
          (fun _proof _checks _exact => rfl) active

theorem runCounted_checks_bounded {Previous : Sort uPrevious}
    (profile : Profile Previous)
    {Output : (previous : Previous) -> profile.Active previous -> Sort uOutput}
    (previous : Previous)
    (onActive : (proof : profile.Active previous) ->
      (checks : Nat) -> checks = profile.selectionBudget.checks previous ->
        Output previous proof) :
    (runCounted profile previous onActive).checks <=
      profile.selectionBudget.coefficient *
        (profile.selectionBudget.size previous + 1) ^
          profile.selectionBudget.degree := by
  rw [runCounted_checks]
  exact profile.selectionBudget.bounded previous

/-- The same branch remains focused after a node extends the ledger. -/
def successor {Previous : Sort uPrevious} (profile : Profile Previous)
    (Output : (previous : Previous) -> profile.Active previous -> Sort uOutput) :
    Profile (Stage profile Output) where
  Active := fun stage => profile.Active stage.previous
  select := fun stage => profile.select stage.previous
  selectionBudget := profile.selectionBudget.comap fun stage => stage.previous
  select_checks := fun stage => profile.select_checks stage.previous

/-! ## Typed reads on an active branch -/

/-- A typed inherited read available only when the source lies on the focus. -/
structure ActiveQuery {Previous : Sort uPrevious} (profile : Profile Previous)
    (Result : (previous : Previous) -> profile.Active previous -> Sort uResult) where
  private mk ::
  read : (previous : Previous) -> (proof : profile.Active previous) ->
    Result previous proof

/-! ## Counted refinement of an existing focus -/

/-- A child predicate and its exact counted decision on an already-active
parent focus. The decision budget is indexed by the literal predecessor; it
is charged only when the parent selector accepts that predecessor. -/
structure Refinement {Previous : Sort uPrevious}
    (profile : Profile Previous) where
  private mk ::
  Predicate : (previous : Previous) -> profile.Active previous -> Prop
  decide : (previous : Previous) -> (active : profile.Active previous) ->
    Counted (Decidable (Predicate previous active))
  decisionBudget : PolynomialCheckBudget Previous
  decide_checks : forall previous active,
    (decide previous active).checks = decisionBudget.checks previous

namespace ActiveQuery

/-- Refine a focus by comparing a finite tag projected from one inherited
query with a fixed expected tag. Core owns the equality decision and charges
exactly one inspection. Callers cannot install an opaque child selector or
claim an unrelated work budget. -/
def tagEqualTo {Previous : Sort uPrevious} {profile : Profile Previous}
    {Input : (previous : Previous) -> profile.Active previous -> Type uResult}
    (query : ActiveQuery profile Input) {Value : Type uOther}
    (tag : (previous : Previous) -> (active : profile.Active previous) ->
      Input previous active -> Value)
    (expected : Value) [DecidableEq Value] : Refinement profile where
  Predicate := fun previous active =>
    tag previous active (query.read previous active) = expected
  decide := fun _previous _active =>
    { value := inferInstance
      checks := 1 }
  decisionBudget := PolynomialCheckBudget.constant (fun _previous => 0) 1
  decide_checks := fun _previous _active => rfl

/-- Equality refinement is the identity-tag specialization of `tagEqualTo`. -/
def equalTo {Previous : Sort uPrevious} {profile : Profile Previous}
    {Value : Type uResult}
    (query : ActiveQuery profile fun _previous _active => Value)
    (expected : Value) [DecidableEq Value] : Refinement profile :=
  query.tagEqualTo (fun _previous _active value => value) expected

end ActiveQuery

/-- Evidence that both the parent focus and its counted child predicate select
the same literal predecessor. -/
structure RefinedActive {Previous : Sort uPrevious}
    {profile : Profile Previous} (refinement : Refinement profile)
    (previous : Previous) : Prop where
  parent : profile.Active previous
  accepted : refinement.Predicate previous parent

/-- Execute the parent selector once and, only on its active branch, execute
the child decision once. No decision is rerun to construct the proof. -/
def selectRefined {Previous : Sort uPrevious}
    (profile : Profile Previous) (refinement : Refinement profile)
    (previous : Previous) :
    Counted (Decidable (RefinedActive refinement previous)) :=
  (profile.select previous).bind fun parentDecision =>
    match parentDecision with
    | .isTrue parent =>
        (refinement.decide previous parent).map fun childDecision =>
          match childDecision with
          | .isTrue accepted => .isTrue ⟨parent, accepted⟩
          | .isFalse rejected =>
              .isFalse fun active => by
                have equal : active.parent = parent := Subsingleton.elim _ _
                cases equal
                exact rejected active.accepted
    | .isFalse absent =>
        Counted.pure (.isFalse fun active => absent active.parent)

/-- An active parent pays exactly one parent selection and one child decision,
independently of whether the child accepts or rejects. -/
theorem selectRefined_checks_of_parent_active {Previous : Sort uPrevious}
    (profile : Profile Previous) (refinement : Refinement profile)
    (previous : Previous) (active : profile.Active previous) :
    (selectRefined profile refinement previous).checks =
      profile.selectionBudget.checks previous +
        refinement.decisionBudget.checks previous := by
  cases selected : (profile.select previous).value with
  | isTrue _parent =>
      simp [selectRefined, selected, Counted.bind, Counted.map,
        profile.select_checks, refinement.decide_checks]
  | isFalse absent => exact (absent active).elim

/-- An inactive parent skips the child decision and pays only the parent
selector. -/
theorem selectRefined_checks_of_parent_inactive {Previous : Sort uPrevious}
    (profile : Profile Previous) (refinement : Refinement profile)
    (previous : Previous) (inactive : Not (profile.Active previous)) :
    (selectRefined profile refinement previous).checks =
      profile.selectionBudget.checks previous := by
  cases selected : (profile.select previous).value with
  | isTrue active => exact (inactive active).elim
  | isFalse _absent =>
      simp [selectRefined, selected, Counted.bind, Counted.pure,
        profile.select_checks]

/-- Exact dynamic selector budget for a refined focus. Inactive parents pay
only the parent selector; active parents pay the parent and child decisions.
The polynomial envelope is the generic sequential sum of both budgets. -/
def refinedSelectionBudget {Previous : Sort uPrevious}
    (profile : Profile Previous) (refinement : Refinement profile) :
    PolynomialCheckBudget Previous :=
  let envelope := profile.selectionBudget.add refinement.decisionBudget
  { size := envelope.size
    checks := fun previous =>
      profile.selectionBudget.checks previous +
        match (profile.select previous).value with
        | .isTrue _active => refinement.decisionBudget.checks previous
        | .isFalse _inactive => 0
    coefficient := envelope.coefficient
    degree := envelope.degree
    bounded := by
      intro previous
      cases selected : (profile.select previous).value with
      | isTrue _active =>
          exact envelope.bounded previous
      | isFalse _inactive =>
          exact (Nat.le_add_right
            (profile.selectionBudget.checks previous)
            (refinement.decisionBudget.checks previous)).trans
              (envelope.bounded previous) }

/-- The independently specified dynamic budget agrees with the actual
single-pass refined selector. -/
theorem selectRefined_checks_eq_budget {Previous : Sort uPrevious}
    (profile : Profile Previous) (refinement : Refinement profile)
    (previous : Previous) :
    (selectRefined profile refinement previous).checks =
      (refinedSelectionBudget profile refinement).checks previous := by
  cases selected : (profile.select previous).value with
  | isTrue _active =>
      simp [selectRefined, refinedSelectionBudget, selected, Counted.bind,
        Counted.map, profile.select_checks, refinement.decide_checks]
  | isFalse _inactive =>
      simp [selectRefined, refinedSelectionBudget, selected, Counted.bind,
        Counted.pure, profile.select_checks]

/-- Narrow a live branch by one counted predicate while retaining the literal
predecessor type and all parent-owned ledger queries. -/
def refine {Previous : Sort uPrevious} (profile : Profile Previous)
    (refinement : Refinement profile) : Profile Previous where
  Active := RefinedActive refinement
  select := selectRefined profile refinement
  selectionBudget := refinedSelectionBudget profile refinement
  select_checks := selectRefined_checks_eq_budget profile refinement

/-- Framework-owned view of one exact focused predecessor.  This is an input
adapter for an existing unfocused executor, not a replacement ledger stage:
the enclosing focused executor still extends the literal `previous` value. -/
structure ActiveView {Previous : Type uPrevious} (profile : Profile Previous) where
  private mk ::
  previous : Previous
  proof : profile.Active previous

namespace ActiveView

/-- Package the predecessor and the exact activity proof selected by Core. -/
def of {Previous : Type uPrevious} {profile : Profile Previous}
    (previous : Previous) (proof : profile.Active previous) :
    ActiveView profile :=
  .mk previous proof

/-- An active view is a temporary root for ordinary typed queries consumed by
existing CT capabilities.  It is never installed in place of the enclosing
accumulated ledger. -/
instance {Previous : Type uPrevious} {profile : Profile Previous} :
    HasResidual (ActiveView profile) (ActiveView profile) where
  residual := id

@[simp] theorem residualOf_of {Previous : Type uPrevious}
    {profile : Profile Previous} (previous : Previous)
    (proof : profile.Active previous) :
    residualOf (of previous proof) = of previous proof :=
  rfl

end ActiveView

namespace ActiveQuery

/-- Reindex an active query over the framework-owned active view.  This lets
an existing CT or domain adapter consume focused predecessor data without an
application-created state object or copied ledger payload. -/
def onView {Previous : Type uPrevious} {profile : Profile Previous}
    {Result : (previous : Previous) -> profile.Active previous -> Sort uResult}
    (query : ActiveQuery profile Result) :
    Query (ActiveView profile)
      (fun view => Result view.previous view.proof) :=
  (Query.residual (Source := ActiveView profile)
    (Residual := ActiveView profile)).map fun view _root =>
      query.read view.previous view.proof

@[simp] theorem read_onView {Previous : Type uPrevious}
    {profile : Profile Previous}
    {Result : (previous : Previous) -> profile.Active previous -> Sort uResult}
    (query : ActiveQuery profile Result) (previous : Previous)
    (proof : profile.Active previous) :
    query.onView.read (ActiveView.of previous proof) =
      query.read previous proof :=
  rfl

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

/-- Reuse a parent-owned active query under a counted refinement without
copying its value into a child payload. -/
def narrow {Previous : Sort uPrevious} {profile : Profile Previous}
    (refinement : Refinement profile)
    {Result : (previous : Previous) -> profile.Active previous -> Sort uResult}
    (query : ActiveQuery profile Result) :
    ActiveQuery (refine profile refinement) fun previous active =>
      Result previous active.parent :=
  .mk fun previous active => query.read previous active.parent

/-- Retrieve the exact child-predicate proof selected by a refined focus. -/
def refinementProof {Previous : Sort uPrevious}
    {profile : Profile Previous} (refinement : Refinement profile) :
    ActiveQuery (refine profile refinement) fun previous active =>
      refinement.Predicate previous active.parent :=
  .mk fun _previous active => active.accepted

/-- Read the exact inherited value and its selected tag equality together.
The value is read once; the equality is the proof retained by the refined
focus. -/
def selectedTag {Previous : Sort uPrevious} {profile : Profile Previous}
    {Input : (previous : Previous) -> profile.Active previous -> Type uResult}
    (query : ActiveQuery profile Input) {Value : Type uOther}
    (tag : (previous : Previous) -> (active : profile.Active previous) ->
      Input previous active -> Value)
    (expected : Value) [DecidableEq Value] :
    ActiveQuery (refine profile (query.tagEqualTo tag expected))
      fun previous active =>
        { value : Input previous active.parent //
          tag previous active.parent value = expected } :=
  .mk fun previous active =>
    ⟨query.read previous active.parent, active.accepted⟩

/-- Retrieve the selected equality from a framework-owned equality
refinement, without exposing the raw refinement constructor. -/
def equalToProof {Previous : Sort uPrevious} {profile : Profile Previous}
    {Value : Type uResult}
    (query : ActiveQuery profile fun _previous _active => Value)
    (expected : Value) [DecidableEq Value] :
    ActiveQuery (refine profile (query.equalTo expected)) fun previous active =>
      query.read previous active.parent = expected :=
  .mk fun _previous active => active.accepted

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
  select := fun stage =>
    { value :=
        match selected : stage.added with
        | .yesBranch proof => .isTrue ⟨proof, selected⟩
        | .noBranch _proof =>
            .isFalse fun active => by
              have contradiction := selected.symm.trans active.selected
              cases contradiction
      checks := 1 }
  selectionBudget := PolynomialCheckBudget.constant (fun _stage => 0) 1
  select_checks := fun _stage => rfl

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
  select := fun stage =>
    { value :=
        match selected : stage.added with
        | .yesBranch _proof =>
            .isFalse fun active => by
              have contradiction := selected.symm.trans active.selected
              cases contradiction
        | .noBranch proof => .isTrue ⟨proof, selected⟩
      checks := 1 }
  selectionBudget := PolynomialCheckBudget.constant (fun _stage => 0) 1
  select_checks := fun _stage => rfl

/-- Retrieve the no proof selected by the focused decision constructor. -/
def noProof {Previous : Sort uPrevious} {Yes No : Previous -> Prop} :
    ActiveQuery (no (Yes := Yes) (No := No)) fun stage _active =>
      No stage.previous :=
  .mk fun _stage active => active.proof

end Hypostructure.Core.Residual.Focus
