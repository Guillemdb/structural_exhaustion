namespace StructuralExhaustion.Core

universe u

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

/-- Canonical zero-copy handoff for an incoming residual. -/
def refl {Previous : Sort u} (previous : Previous) : ExactHandoff previous where
  previous := previous
  previousExact := rfl

@[simp] theorem previous_eq {Previous : Sort u} {expected : Previous}
    (handoff : ExactHandoff expected) : handoff.previous = expected :=
  handoff.previousExact

/-- Transport a theorem about the named predecessor to the retained value. -/
theorem property {Previous : Sort u} {expected : Previous}
    (handoff : ExactHandoff expected) (Property : Previous → Prop)
    (proved : Property expected) : Property handoff.previous := by
  simpa [handoff.previousExact] using proved

end ExactHandoff

end StructuralExhaustion.Core
