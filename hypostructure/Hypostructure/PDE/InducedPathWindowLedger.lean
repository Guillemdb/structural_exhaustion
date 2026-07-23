import Hypostructure.PDE.InducedPathMaximalPacking

/-!# PDE induced-path window ledgers

The ledger is the PDE counterpart of graph window surplus accounting.  A
represented path family supplies finite windows, local charges, and a
capacity; the generic API exposes aggregate mass and overload without
assuming a particular norm or continuum decomposition.
-/

namespace Hypostructure.PDE.InducedPathWindowLedger

universe uPrevious uEvent uPath uWindow

open Hypostructure

structure Profile (Previous : Type uPrevious) where
  Window : Previous -> Type uWindow
  Path : Previous -> Type uPath
  schedule : Core.Residual.Query Previous
    (fun previous => Core.Finite.Enumeration (Window previous))
  path : (previous : Previous) -> Window previous -> Path previous
  charge : (previous : Previous) -> Window previous -> Int
  capacity : (previous : Previous) -> Window previous -> Int
  chargeDecidable : (previous : Previous) ->
    (window : Window previous) -> Decidable (charge previous window ≥ 0)

def totalCharge (profile : Profile Previous) (previous : Previous) : Int :=
  (profile.schedule.read previous).values.map (profile.charge previous) |>.sum

def totalCapacity (profile : Profile Previous) (previous : Previous) : Int :=
  (profile.schedule.read previous).values.map (profile.capacity previous) |>.sum

def overload (profile : Profile Previous) (previous : Previous) : Prop :=
  totalCharge profile previous > totalCapacity profile previous

theorem overload_iff
    (profile : Profile Previous) (previous : Previous) :
    overload profile previous ↔
      totalCapacity profile previous < totalCharge profile previous :=
  Iff.rfl

end Hypostructure.PDE.InducedPathWindowLedger
