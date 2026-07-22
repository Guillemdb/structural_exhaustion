import Hypostructure.Core.Residual.Query

/-!
# Dynamic budgets

Core owns the residual-indexed notion of a budgeted quantity.  The quantity
itself can be graph charge, PDE energy, or any other ordered value; Graph and
PDE only specialize the payload and the order relation.
-/

namespace Hypostructure.Core.Budget.Dynamic

universe uPrevious uPrevious' uQuantity uNewQuantity

open Hypostructure.Core.Residual

/-- A residual-indexed quantity together with its residual-indexed budget.
The comparison is intentionally generic so graph charge and PDE energy can
share the same Core contract. -/
structure Profile (Previous : Sort uPrevious) (Quantity : Type uQuantity)
    [Preorder Quantity] where
  value : Query Previous (fun _previous => Quantity)
  budget : Query Previous (fun _previous => Quantity)
  within : forall previous, value.read previous <= budget.read previous

namespace Profile

variable {Previous : Sort uPrevious} {Quantity : Type uQuantity}
variable {Previous' : Sort uPrevious'}
variable {NewQuantity : Type uNewQuantity}
variable [Preorder Quantity] [Preorder NewQuantity]

/-- Reindex a dynamic budget profile along a predecessor projection. -/
def reindex
    (project : Previous' -> Previous)
    (profile : Profile Previous Quantity) :
    Profile Previous' Quantity where
  value := profile.value.comap project
  budget := profile.budget.comap project
  within := by
    intro previous'
    exact profile.within (project previous')

/-- Remap a dynamic budget profile through a monotone quantity morphism. -/
def map
    (f : Quantity -> NewQuantity) (monotone : Monotone f)
    (profile : Profile Previous Quantity) :
    Profile Previous NewQuantity where
  value := profile.value.map fun _ => f
  budget := profile.budget.map fun _ => f
  within := by
    intro previous
    exact monotone (profile.within previous)

@[simp]
theorem reindex_read_value (project : Previous' -> Previous)
    (profile : Profile Previous Quantity) (previous' : Previous') :
    (reindex (Previous := Previous) (Quantity := Quantity) project profile).value.read previous'
      = profile.value.read (project previous') := rfl

@[simp]
theorem reindex_read_budget (project : Previous' -> Previous)
    (profile : Profile Previous Quantity) (previous' : Previous') :
    (reindex (Previous := Previous) (Quantity := Quantity) project profile).budget.read previous'
      = profile.budget.read (project previous') := rfl

@[simp]
theorem map_read_value (f : Quantity -> NewQuantity)
    (monotone : Monotone f) (profile : Profile Previous Quantity)
    (previous : Previous) :
    (map (Quantity := Quantity) (NewQuantity := NewQuantity) f monotone profile).value.read previous
      = f (profile.value.read previous) := rfl

@[simp]
theorem map_read_budget (f : Quantity -> NewQuantity)
    (monotone : Monotone f) (profile : Profile Previous Quantity)
    (previous : Previous) :
    (map (Quantity := Quantity) (NewQuantity := NewQuantity) f monotone profile).budget.read previous
      = f (profile.budget.read previous) := rfl

def current (profile : Profile Previous Quantity) (previous : Previous) :
    Quantity :=
  profile.value.read previous

def limit (profile : Profile Previous Quantity) (previous : Previous) :
    Quantity :=
  profile.budget.read previous

theorem current_le_limit (profile : Profile Previous Quantity)
    (previous : Previous) :
    profile.current previous <= profile.limit previous :=
  profile.within previous

end Profile

variable {Previous : Sort uPrevious} {Quantity : Type uQuantity}
variable {Previous' : Sort uPrevious'}
variable [Preorder Quantity]
variable {NewQuantity : Type uNewQuantity} [Preorder NewQuantity]

/-- Core-level projection for a residual-indexed dynamic budget. -/
def current (profile : Profile Previous Quantity) (previous : Previous) :
    Quantity :=
  profile.current previous

/-- Core-level budget limit for a residual-indexed dynamic budget. -/
def limit (profile : Profile Previous Quantity) (previous : Previous) :
    Quantity :=
  profile.limit previous

theorem current_le_limit (profile : Profile Previous Quantity)
    (previous : Previous) :
    current profile previous <= limit profile previous :=
  profile.current_le_limit previous

@[simp]
theorem Profile.reindex_current
    (project : Previous' -> Previous) (profile : Profile Previous Quantity)
    (previous' : Previous') :
    (current (Profile.reindex (Previous := Previous) (Quantity := Quantity) project profile) previous')
      = profile.value.read (project previous') := rfl

@[simp]
theorem Profile.reindex_limit
    (project : Previous' -> Previous) (profile : Profile Previous Quantity)
    (previous' : Previous') :
    (limit (Profile.reindex (Previous := Previous) (Quantity := Quantity) project profile) previous')
      = profile.budget.read (project previous') := rfl

@[simp]
theorem Profile.map_current
    (f : Quantity -> NewQuantity)
    (monotone : Monotone f) (profile : Profile Previous Quantity)
    (previous : Previous) :
    (current (Profile.map (Quantity := Quantity) (NewQuantity := NewQuantity) f monotone profile)
      previous) = f (profile.value.read previous) := rfl

@[simp]
theorem Profile.map_limit
    (f : Quantity -> NewQuantity)
    (monotone : Monotone f) (profile : Profile Previous Quantity)
    (previous : Previous) :
    (limit (Profile.map (Quantity := Quantity) (NewQuantity := NewQuantity) f monotone profile)
      previous) = f (profile.budget.read previous) := rfl

end Hypostructure.Core.Budget.Dynamic
