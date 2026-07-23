import Hypostructure.Core.Finite.Enumeration
import Hypostructure.Core.Residual.Query

/-!# PDE induced transition paths

This is the PDE counterpart of a finite induced graph path.  A represented
application supplies the finite event schedule and its transition relation;
the certificate records an ordered chain, pairwise distinctness, and induced
adjacency.  No ambient continuum is enumerated.
-/

namespace Hypostructure.PDE.InducedPath

universe uPrevious uEvent

open Hypostructure

structure Profile (Previous : Type uPrevious) where
  Event : Previous -> Type uEvent
  schedule : Core.Residual.Query Previous
    (fun previous => Core.Finite.Enumeration (Event previous))
  adjacent : (previous : Previous) -> Event previous -> Event previous -> Prop
  adjacentDecidable : (previous : Previous) ->
    (left right : Event previous) -> Decidable (adjacent previous left right)

structure Certificate (profile : Profile Previous) (previous : Previous) where
  values : List (profile.Event previous)
  scheduled : ∀ value, value ∈ values ->
    value ∈ (profile.schedule.read previous).values
  nodup : values.Nodup
  chain : values.Pairwise (profile.adjacent previous)
  induced : ∀ {left right}, left ∈ values -> right ∈ values ->
    left ≠ right -> profile.adjacent previous left right

def Has (profile : Profile Previous) (previous : Previous) : Prop :=
  Nonempty (Certificate profile previous)

noncomputable def Has.decide (profile : Profile Previous) (previous : Previous) :
    Decidable (Has profile previous) := by
  classical
  unfold Has
  infer_instance

theorem values_are_scheduled
    (profile : Profile Previous) (previous : Previous)
    (certificate : Certificate profile previous) :
    ∀ value ∈ certificate.values,
      value ∈ (profile.schedule.read previous).values :=
  certificate.scheduled

theorem chain_pair
    (profile : Profile Previous) (previous : Previous)
    (certificate : Certificate profile previous)
    {left right : profile.Event previous}
    (leftMem : left ∈ certificate.values)
    (rightMem : right ∈ certificate.values)
    (different : left ≠ right) :
    profile.adjacent previous left right :=
  certificate.induced leftMem rightMem different

end Hypostructure.PDE.InducedPath
