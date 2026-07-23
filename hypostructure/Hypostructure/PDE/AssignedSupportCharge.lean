import Hypostructure.Core.Finite.Enumeration
import Hypostructure.Core.Residual.Query
import Hypostructure.PDE.Model

/-!
# PDE assigned support charges

The Graph layer assigns each finite support item to a support account.  PDE
uses the same accounting surface for energy channels, flux windows, defect
classes, and profile packets.  The assignment and charge semantics are
application data; the finite aggregate is framework-visible bookkeeping.
-/

namespace Hypostructure.PDE.AssignedSupportCharge

universe uPrevious uModel uItem uSupport

structure Profile {Previous : Type uPrevious}
    (M : PDE.LocalModel.{uModel}) where
  Item : Previous -> Type uItem
  Support : Previous -> Type uSupport
  items : Core.Residual.Query Previous
    (fun previous => Core.Finite.Enumeration (Item previous))
  support : (previous : Previous) -> Item previous -> Support previous
  charge : (previous : Previous) -> Item previous -> Int
  state : Core.Residual.Query Previous (fun _ => M.problem.Ambient)
  admissible : (previous : Previous) -> M.problem.Ambient ->
    Item previous -> Prop
  admissibleDecidable : (previous : Previous) ->
    (object : M.problem.Ambient) -> (item : Item previous) ->
      Decidable (admissible previous object item)

def totalCharge {Previous : Type uPrevious}
    {M : PDE.LocalModel.{uModel}}
    (profile : Profile (M := M) (Previous := Previous))
    (previous : Previous) : Int :=
  (profile.items.read previous).values.map
    (profile.charge previous) |>.sum

def admissibleItems {Previous : Type uPrevious}
    {M : PDE.LocalModel.{uModel}}
    (profile : Profile (M := M) (Previous := Previous))
    (previous : Previous) : List (profile.Item previous) := by
  letI : ∀ item, Decidable (profile.admissible previous
      (profile.state.read previous) item) :=
    fun item => profile.admissibleDecidable previous
      (profile.state.read previous) item
  exact (profile.items.read previous).values.filter
    (fun item => decide (profile.admissible previous
      (profile.state.read previous) item))

end Hypostructure.PDE.AssignedSupportCharge
