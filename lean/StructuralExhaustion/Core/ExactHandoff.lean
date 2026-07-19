namespace StructuralExhaustion.Core

universe u v

/-!
# Exact predecessor handoffs

Proof-diagram nodes frequently retain their incoming residual unchanged while
adding one local theorem or decision.  This proof-indexed carrier centralizes
that plumbing.  It performs no computation, changes no residual, and creates
no branch.
-/

/-- One predecessor value together with kernel evidence that it is exactly the
value named by the incoming diagram edge. -/
structure ExactHandoff {Previous : Sort u} (expected : Previous) where
  previous : Previous
  previousExact : previous = expected

namespace ExactHandoff

/-- Exact handoffs over a proof-irrelevant predecessor carry no additional
choice.  This lets proposition-only manuscript prefixes use the same kernel
handoff without application-level equality bookkeeping. -/
instance subsingleton {Previous : Sort u} [Subsingleton Previous]
    {expected : Previous} : Subsingleton (ExactHandoff expected) where
  allEq := by
    rintro ⟨previous, previousExact⟩ ⟨other, otherExact⟩
    have valueEq : previous = other := Subsingleton.elim _ _
    subst valueEq
    have proofEq : previousExact = otherExact := Subsingleton.elim _ _
    subst proofEq
    rfl

/-- Canonical zero-copy handoff for an incoming residual. -/
def refl {Previous : Sort u} (previous : Previous) : ExactHandoff previous where
  previous := previous
  previousExact := rfl

@[simp] theorem previous_eq {Previous : Sort u} {expected : Previous}
    (handoff : ExactHandoff expected) : handoff.previous = expected :=
  handoff.previousExact

/-- Output-oriented view used when an exact handoff is stored as a produced
certificate stage rather than described as an incoming edge. -/
def output {Previous : Sort u} {expected : Previous}
    (handoff : ExactHandoff expected) : Previous :=
  handoff.previous

@[simp] theorem outputExact {Previous : Sort u} {expected : Previous}
    (handoff : ExactHandoff expected) : handoff.output = expected :=
  handoff.previousExact

/-- Transport a theorem about the named predecessor to the retained value. -/
theorem property {Previous : Sort u} {expected : Previous}
    (handoff : ExactHandoff expected) (Property : Previous → Prop)
    (proved : Property expected) : Property handoff.previous := by
  simpa [handoff.previousExact] using proved

/-- Lift an existentially selected context while retaining its guard.  This
owns the common endpoint pattern that preserves a selected context and rank
bound while extending only its proof prefix. -/
theorem exists_and_map {Index : Sort u}
    {guard previous next : Index → Prop}
    (source : ∃ index, guard index ∧ previous index)
    (extend : ∀ index, previous index → next index) :
    ∃ index, guard index ∧ next index := by
  rcases source with ⟨index, guarded, value⟩
  exact ⟨index, guarded, extend index value⟩

end ExactHandoff

/-- An exact predecessor handoff augmented by one proof about the literal
retained predecessor.  Diagram applications use this carrier whenever a node
does not change its residual and adds only a proposition.  The framework owns
the equality transport, so the application stores no bespoke predecessor
bookkeeping. -/
structure ExactPropertyHandoff {Previous : Sort u} (expected : Previous)
    (Property : Previous → Prop) extends ExactHandoff expected where
  certificate : Property previous

namespace ExactPropertyHandoff

/-- Canonical property-producing node on an unchanged predecessor. -/
def refl {Previous : Sort u} {Property : Previous → Prop}
    (previous : Previous) (certificate : Property previous) :
    ExactPropertyHandoff previous Property where
  previous := previous
  previousExact := rfl
  certificate := certificate

/-- Read the retained property at the predecessor named by the incoming
diagram edge. -/
def certificateAtExpected {Previous : Sort u} {expected : Previous}
    {Property : Previous → Prop}
    (handoff : ExactPropertyHandoff expected Property) : Property expected :=
  Eq.mp (congrArg Property handoff.previousExact) handoff.certificate

@[simp] theorem certificateAtExpected_refl {Previous : Sort u}
    {Property : Previous → Prop} (previous : Previous)
    (certificate : Property previous) :
    (refl previous certificate).certificateAtExpected = certificate :=
  rfl

end ExactPropertyHandoff

/-- An exact predecessor handoff paired with one stage whose type may depend
on the retained predecessor. -/
structure ExactStageHandoff {Previous : Sort u} (expected : Previous)
    (Stage : Previous → Sort v) extends ExactHandoff expected where
  stage : Stage previous

namespace ExactStageHandoff

def refl {Previous : Sort u} {Stage : Previous → Sort v}
    (previous : Previous) (stage : Stage previous) :
    ExactStageHandoff previous Stage where
  previous := previous
  previousExact := rfl
  stage := stage

/-- View the dependent stage at the named incoming predecessor. -/
def stageAtExpected {Previous : Sort u} {expected : Previous}
    {Stage : Previous → Sort v}
    (handoff : ExactStageHandoff expected Stage) : Stage expected :=
  Eq.mp (congrArg Stage handoff.previousExact) handoff.stage

/-- Run a dependent producer on the exact predecessor value retained by a
handoff, then transport the result to the predecessor named by the incoming
diagram edge.  Applications therefore consume the retrieved predecessor
instead of recomputing a canonical copy. -/
def transportProducer {Previous : Sort u} {Stage : Previous → Sort v}
    {previous expected : Previous} (previousExact : previous = expected)
    (produce : (value : Previous) → Stage value) : Stage expected :=
  Eq.mp (congrArg Stage previousExact) (produce previous)

@[simp] theorem transportProducer_eq {Previous : Sort u}
    {Stage : Previous → Sort v} {previous expected : Previous}
    (previousExact : previous = expected)
    (produce : (value : Previous) → Stage value) :
    transportProducer previousExact produce = produce expected := by
  cases previousExact
  rfl

@[simp] theorem stageAtExpected_refl {Previous : Sort u}
    {Stage : Previous → Sort v} (previous : Previous)
    (stage : Stage previous) :
    (refl previous stage).stageAtExpected = stage :=
  rfl

end ExactStageHandoff

namespace ExactHandoff

/-- Produce the next predecessor-indexed stage from the literal retained
value and package the transported result as another exact handoff.  This is
the canonical framework operation for a sequential dependent node chain. -/
def mapDependent {Previous : Sort u} {Stage : Previous → Sort v}
    {expected : Previous} (handoff : ExactHandoff expected)
    (produce : (value : Previous) → Stage value) :
    ExactHandoff (produce expected) where
  previous := ExactStageHandoff.transportProducer
    handoff.previousExact produce
  previousExact := ExactStageHandoff.transportProducer_eq
    handoff.previousExact produce

/-- Rename the expected value of an exact handoff along a proved equality.
This owns the common final normalization from a successor expression to the
canonical name assigned to that successor by an application. -/
def castExpected {Previous : Sort u} {expected next : Previous}
    (handoff : ExactHandoff expected) (expectedExact : expected = next) :
    ExactHandoff next where
  previous := handoff.previous
  previousExact := handoff.previousExact.trans expectedExact

@[simp] theorem castExpected_output {Previous : Sort u}
    {expected next : Previous} (handoff : ExactHandoff expected)
    (expectedExact : expected = next) :
    (handoff.castExpected expectedExact).output = next :=
  (handoff.castExpected expectedExact).outputExact

@[simp] theorem mapDependent_output {Previous : Sort u}
    {Stage : Previous → Sort v} {expected : Previous}
    (handoff : ExactHandoff expected)
    (produce : (value : Previous) → Stage value) :
    (handoff.mapDependent produce).output = produce expected :=
  (handoff.mapDependent produce).outputExact

end ExactHandoff

end StructuralExhaustion.Core
