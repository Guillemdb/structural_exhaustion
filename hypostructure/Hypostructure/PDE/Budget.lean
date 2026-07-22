import Hypostructure.Core.Budget.Dynamic

/-!
# PDE budget umbrella

PDE reuses the Core dynamic-budget contract for any ordered quantity, such as
energy, flux, or another residual-owned analytic size.  The PDE layer does not
add a separate accounting shape.
-/

namespace Hypostructure.PDE.Budget

universe uPrevious uPrevious' uQuantity uNewQuantity

/-- PDE-facing dynamic budgets are the Core residual-indexed quantity/limit
profile. -/
abbrev Profile (Previous : Sort uPrevious) (Quantity : Type uQuantity)
    [Preorder Quantity] :=
  Core.Budget.Dynamic.Profile Previous Quantity

/-- Alias kept for API parity with `Graph.Budget` and similar wrappers. -/
abbrev DynamicProfile (Previous : Sort uPrevious) (Quantity : Type uQuantity)
    [Preorder Quantity] :=
  Core.Budget.Dynamic.Profile Previous Quantity

namespace Profile

variable {Previous : Sort uPrevious} {Quantity : Type uQuantity}
variable {Previous' : Sort uPrevious'}
variable {NewQuantity : Type uNewQuantity}
variable [Preorder Quantity] [Preorder NewQuantity]

def reindex
    {Previous' : Sort uPrevious'}
    (project : Previous' -> Previous)
    (profile : Profile Previous Quantity) :
    Profile Previous' Quantity :=
  Core.Budget.Dynamic.Profile.reindex (Previous := Previous)
    (Quantity := Quantity) project profile

def map
    (f : Quantity -> NewQuantity)
    (monotone : Monotone f)
    (profile : Profile Previous Quantity) :
    Profile Previous NewQuantity :=
  Core.Budget.Dynamic.Profile.map (Previous := Previous)
    (Quantity := Quantity) (NewQuantity := NewQuantity) f monotone profile

end Profile

def current {Previous : Sort uPrevious} {Quantity : Type uQuantity}
    [Preorder Quantity] (profile : Profile Previous Quantity)
    (previous : Previous) : Quantity :=
  Core.Budget.Dynamic.current profile previous

def limit {Previous : Sort uPrevious} {Quantity : Type uQuantity}
    [Preorder Quantity] (profile : Profile Previous Quantity)
    (previous : Previous) : Quantity :=
  Core.Budget.Dynamic.limit profile previous

theorem current_le_limit {Previous : Sort uPrevious}
    {Quantity : Type uQuantity} [Preorder Quantity]
    (profile : Profile Previous Quantity) (previous : Previous) :
    current profile previous <= limit profile previous :=
  Core.Budget.Dynamic.current_le_limit profile previous

end Hypostructure.PDE.Budget
