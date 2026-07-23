import Hypostructure.PDE.InducedPath

/-!# PDE maximal packings of induced transition paths

Packing is intentionally a certificate over a finite residual schedule.  The
application decides when two represented chains overlap and when every
scheduled event is covered or conflicts with an already selected chain.
-/

namespace Hypostructure.PDE.InducedPathMaximalPacking

universe uPrevious uEvent uPath

open Hypostructure

structure Profile (Previous : Type uPrevious) where
  Event : Previous -> Type uEvent
  Path : Previous -> Type uPath
  schedule : Core.Residual.Query Previous
    (fun previous => Core.Finite.Enumeration (Event previous))
  support : (previous : Previous) -> Path previous -> List (Event previous)
  valid : (previous : Previous) -> Path previous -> Prop
  overlap : (previous : Previous) -> Path previous -> Path previous -> Prop
  covered : (previous : Previous) -> Event previous -> Path previous -> Prop
  validDecidable : (previous : Previous) -> (path : Path previous) ->
    Decidable (valid previous path)
  overlapDecidable : (previous : Previous) ->
    (left right : Path previous) -> Decidable (overlap previous left right)
  coveredDecidable : (previous : Previous) ->
    (event : Event previous) -> (path : Path previous) ->
      Decidable (covered previous event path)

structure Certificate (profile : Profile Previous) (previous : Previous) where
  paths : List (profile.Path previous)
  validPaths : ∀ path, path ∈ paths -> profile.valid previous path
  pairwiseDisjoint : paths.Pairwise (fun left right =>
    ¬ profile.overlap previous left right)
  maximal : ∀ event ∈ (profile.schedule.read previous).values,
    (∃ path ∈ paths, profile.covered previous event path) ∨
      (∃ path ∈ paths, profile.overlap previous path path)

def Has (profile : Profile Previous) (previous : Previous) : Prop :=
  Nonempty (Certificate profile previous)

noncomputable def Has.decide (profile : Profile Previous) (previous : Previous) :
    Decidable (Has profile previous) := by
  classical
  unfold Has
  infer_instance

theorem valid_of_mem
    (profile : Profile Previous) (previous : Previous)
    (certificate : Certificate profile previous)
    {path : profile.Path previous} (membership : path ∈ certificate.paths) :
    profile.valid previous path :=
  certificate.validPaths path membership

end Hypostructure.PDE.InducedPathMaximalPacking
