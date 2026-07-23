import Hypostructure.PDE.Boundary

/-!
# Arbitrary local PDE response coordinates

This is the PDE counterpart of Graph's atom-response layer.  A coordinate is
any represented local piece with a certified interface label; its meaning is
read only after assembly with a literal outside context.  The specialization
does not enumerate functions, domains, or contexts.
-/

namespace Hypostructure.PDE.AtomResponse

universe u uInterface uPiece uOutside

open Hypostructure

structure CoordinateSystem
    {P : Core.Problem.{u, u}}
    (decomposition : PDE.Boundary.Decomposition P)
    (Target : P.Ambient -> Prop) where
  Coordinate : Type uPiece
  label : decomposition.interface.Label
  represented : Coordinate -> decomposition.Piece label
  registered : Coordinate -> Prop
  registered_decidable : (coordinate : Coordinate) -> Decidable (registered coordinate)
  assemble : Coordinate -> decomposition.Outside label -> P.Ambient :=
    fun coordinate outside => decomposition.assemble label
      (represented coordinate) outside

namespace CoordinateSystem

variable {P : Core.Problem.{u, u}}
variable {decomposition : PDE.Boundary.Decomposition P}
variable {Target : P.Ambient -> Prop}

def targetResponse
    (system : CoordinateSystem decomposition Target)
    (coordinate : system.Coordinate)
    (outside : decomposition.Outside system.label) : Prop :=
  Target (decomposition.assemble system.label
    (system.represented coordinate) outside)

def ContextEquivalent
    (system : CoordinateSystem decomposition Target)
    (left right : system.Coordinate) : Prop :=
    ∀ outside : decomposition.Outside system.label,
    system.targetResponse left outside ↔
      system.targetResponse right outside

theorem targetResponse_eq
    (system : CoordinateSystem decomposition Target)
    (coordinate : system.Coordinate)
    (outside : decomposition.Outside system.label) :
    system.targetResponse coordinate outside =
      Target (decomposition.assemble system.label
        (system.represented coordinate) outside) :=
  rfl

end CoordinateSystem

structure TargetCompleteQuotient
    {P : Core.Problem.{u, u}}
    {decomposition : PDE.Boundary.Decomposition P}
    {Target : P.Ambient -> Prop}
    (system : CoordinateSystem decomposition Target) where
  relation : Setoid system.Coordinate
  context_complete : ∀ {left right}, relation.r left right ->
    system.ContextEquivalent left right

namespace TargetCompleteQuotient

variable {P : Core.Problem.{u, u}}
variable {decomposition : PDE.Boundary.Decomposition P}
variable {Target : P.Ambient -> Prop}
variable {system : CoordinateSystem decomposition Target}

abbrev Carrier (quotient : TargetCompleteQuotient system) : Type uPiece :=
  Quotient quotient.relation

def Identified (quotient : TargetCompleteQuotient system)
    (left right : system.Coordinate) : Prop :=
  quotient.relation.r left right

theorem contextUniversal_of_identified
    (quotient : TargetCompleteQuotient system)
    {left right : system.Coordinate}
    (identified : quotient.Identified left right) :
    system.ContextEquivalent left right :=
  quotient.context_complete identified

end TargetCompleteQuotient

def TargetCompleteIdentification
    {P : Core.Problem.{u, u}}
    {decomposition : PDE.Boundary.Decomposition P}
    {Target : P.Ambient -> Prop}
    (system : CoordinateSystem decomposition Target)
    (left right : system.Coordinate) : Prop :=
  ∃ quotient : TargetCompleteQuotient system,
    quotient.Identified left right

def TargetDefect
    {P : Core.Problem.{u, u}}
    {decomposition : PDE.Boundary.Decomposition P}
    {Target : P.Ambient -> Prop}
    (system : CoordinateSystem decomposition Target)
    (left right : system.Coordinate) : Prop :=
  ∃ outside, ¬ (system.targetResponse left outside ↔
    system.targetResponse right outside)

theorem targetDefect_of_not_contextEquivalent
    {P : Core.Problem.{u, u}}
    {decomposition : PDE.Boundary.Decomposition P}
    {Target : P.Ambient -> Prop}
    {system : CoordinateSystem decomposition Target}
    {left right : system.Coordinate}
    (failure : ¬ system.ContextEquivalent left right) :
    TargetDefect system left right := by
  simp only [CoordinateSystem.ContextEquivalent, not_forall] at failure
  exact failure

end Hypostructure.PDE.AtomResponse
