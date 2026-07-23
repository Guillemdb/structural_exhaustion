import Hypostructure.Core.Problem
import Hypostructure.Core.Progress
import Hypostructure.PDE.Model
import Hypostructure.PDE.Representation

/-!
# PDE interfaces, local pieces, and gluing

This is the continuum counterpart of the Graph boundary/gluing layer.  An
interface may represent a trace, a pressure gauge, a flux datum, or a local
window boundary.  The API never enumerates the ambient domain or outside
contexts; an application supplies only the exact assembly and transport laws.
-/

namespace Hypostructure.PDE.Boundary

universe u uInterface uPiece uOutside

structure Interface where
  Label : Type uInterface

structure Decomposition (P : Core.Problem.{u, u}) where
  interface : Interface.{uInterface}
  Piece : interface.Label -> Type uPiece
  Outside : interface.Label -> Type uOutside
  assemble : (label : interface.Label) -> Piece label -> Outside label ->
    P.Ambient
  compatible : P.Ambient -> interface.Label -> Prop
  decompose : (object : P.Ambient) ->
    (label : interface.Label) × Piece label × Outside label
  reconstruct : forall (object : P.Ambient),
    compatible object (decompose object).1 ->
      assemble (decompose object).1 (decompose object).2.1
        (decompose object).2.2 = object

def Context (D : Decomposition P) (label : D.interface.Label) := D.Outside label

def Piece (D : Decomposition P) (label : D.interface.Label) := D.Piece label

def assemble {P : Core.Problem.{u, u}} (D : Decomposition P)
    {label : D.interface.Label} : D.Piece label -> D.Outside label -> P.Ambient :=
  D.assemble label

structure ReplacementCertificate
    {P : Core.Problem.{u, u}}
    (D : Decomposition P)
    (Target : P.Ambient -> Prop)
    (progress : Core.Progress P)
    {label : D.interface.Label}
    (source replacement : D.Piece label) where
  /-- The model's typed trace/flux/gauge equivalence on pieces. -/
  interfaceRelation : D.Piece label -> D.Piece label -> Prop
  sameInterface : interfaceRelation source replacement
  baselineTransport : forall outside,
    P.Baseline (D.assemble label source outside) ->
      P.Baseline (D.assemble label replacement outside)
  responseTransport : forall outside,
    Target (D.assemble label replacement outside) ->
      Target (D.assemble label source outside)
  strictlySmaller : forall outside,
    progress.Smaller (D.assemble label replacement outside)
      (D.assemble label source outside)

end Hypostructure.PDE.Boundary
