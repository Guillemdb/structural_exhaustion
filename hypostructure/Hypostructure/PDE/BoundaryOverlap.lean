import Hypostructure.PDE.Boundary

/-!# PDE interface-overlap profiles

Unlike Graph, PDE interfaces need not have a canonical edge graph.  The two
sides therefore expose their shared interface contribution as a supplied
finite or represented predicate.  This keeps overlap accounting reusable for
traces, fluxes, gauges, and local-window boundaries.
-/

namespace Hypostructure.PDE.BoundaryOverlap

universe u uInterface uPiece uOutside uOverlap

structure Profile {P : Core.Problem.{u, u}}
    (D : PDE.Boundary.Decomposition P)
    (label : D.interface.Label) where
  Overlap : Type uOverlap
  pieceOwns : D.Piece label -> Overlap -> Prop
  outsideOwns : D.Outside label -> Overlap -> Prop
  pieceOwnsDecidable : (piece : D.Piece label) ->
    (overlap : Overlap) -> Decidable (pieceOwns piece overlap)
  outsideOwnsDecidable : (outside : D.Outside label) ->
    (overlap : Overlap) -> Decidable (outsideOwns outside overlap)

def shared {P : Core.Problem.{u, u}} {D : PDE.Boundary.Decomposition P}
    {label : D.interface.Label} (profile : Profile D label)
    (piece : D.Piece label) (outside : D.Outside label) :
    profile.Overlap -> Prop :=
  fun overlap => profile.pieceOwns piece overlap ∧
    profile.outsideOwns outside overlap

theorem shared_iff {P : Core.Problem.{u, u}}
    {D : PDE.Boundary.Decomposition P} {label : D.interface.Label}
    (profile : Profile D label) (piece : D.Piece label)
    (outside : D.Outside label) (overlap : profile.Overlap) :
    shared profile piece outside overlap ↔
      profile.pieceOwns piece overlap ∧ profile.outsideOwns outside overlap :=
  Iff.rfl

theorem shared_empty_of_outside_disjoint
    {P : Core.Problem.{u, u}} {D : PDE.Boundary.Decomposition P}
    {label : D.interface.Label} (profile : Profile D label)
    (piece : D.Piece label) (outside : D.Outside label)
    (disjoint : ∀ overlap, ¬ profile.outsideOwns outside overlap) :
    ∀ overlap, ¬ shared profile piece outside overlap := by
  intro overlap sharedOverlap
  exact disjoint overlap sharedOverlap.2

end Hypostructure.PDE.BoundaryOverlap
