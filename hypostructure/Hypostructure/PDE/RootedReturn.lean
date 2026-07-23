import Hypostructure.Core.Finite.Enumeration
import Hypostructure.Core.Residual.Query

/-!# PDE rooted-return target algebra

Graph has an edge-rooted return because deleting a root edge leaves a path
back to its tail.  PDE models need the same reusable target algebra for
re-entry into a scale, chart, profile, or local packet after a certified
transition.  The transition semantics remain model-owned; this module owns
only the finite, proof-carrying witness shape and its schedule algebra.
-/

namespace Hypostructure.PDE.RootedReturn

universe uPrevious uState uEvent uLength

open Hypostructure

structure Profile (Previous : Type uPrevious) where
  State : Previous -> Type uState
  Event : Previous -> Type uEvent
  Length : Previous -> Type uLength
  state : Previous -> State previous
  events : Core.Residual.Query Previous
    (fun previous => Core.Finite.Enumeration (Event previous))
  length : (previous : Previous) -> Event previous -> Length previous
  root : (previous : Previous) -> Event previous -> Prop
  returns : (previous : Previous) -> Event previous -> Event previous -> Prop
  rootDecidable : (previous : Previous) -> (event : Event previous) ->
    Decidable (root previous event)
  returnsDecidable : (previous : Previous) -> (first second : Event previous) ->
    Decidable (returns previous first second)

structure Certificate (profile : Profile Previous) (previous : Previous) where
  rootEvent : profile.Event previous
  returnEvent : profile.Event previous
  rootMem : rootEvent ∈ (profile.events.read previous).values
  returnMem : returnEvent ∈ (profile.events.read previous).values
  rootEvidence : profile.root previous rootEvent
  returnEvidence : profile.returns previous rootEvent returnEvent

def Has (profile : Profile Previous) (previous : Previous) : Prop :=
  Nonempty (Certificate profile previous)

noncomputable def Has.decide (profile : Profile Previous) (previous : Previous) :
    Decidable (Has profile previous) := by
  classical
  unfold Has
  infer_instance

theorem has_iff_exists
    (profile : Profile Previous) (previous : Previous) :
    Has profile previous ↔
    ∃ rootEvent ∈ (profile.events.read previous).values,
        ∃ returnEvent ∈ (profile.events.read previous).values,
          profile.root previous rootEvent ∧
            profile.returns previous rootEvent returnEvent := by
  constructor
  · rintro ⟨certificate⟩
    exact ⟨certificate.rootEvent,
      certificate.rootMem,
      certificate.returnEvent,
      certificate.returnMem,
      certificate.rootEvidence, certificate.returnEvidence⟩
  · rintro ⟨rootEvent, rootMem, returnEvent, returnMem, rootEvidence,
      returnEvidence⟩
    exact ⟨⟨rootEvent, returnEvent, rootMem, returnMem, rootEvidence,
      returnEvidence⟩⟩

end Hypostructure.PDE.RootedReturn
