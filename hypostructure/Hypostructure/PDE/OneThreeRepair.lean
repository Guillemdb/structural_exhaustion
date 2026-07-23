import Hypostructure.Core.AffineBalance
import Hypostructure.PDE.Model

/-!
# PDE affine one--three repair

Graph derives a one--three identity from degrees.  PDE supplies the analogous
energy/flux/rank quantities and their exact balance laws; Core performs the
same algebraic elimination.  No PDE theorem is assumed by this adapter.
-/

namespace Hypostructure.PDE.OneThreeRepair

universe u

structure Component (P : Core.Problem.{u, u}) where
  internal : Int
  surplus : Int
  boundary : Int
  total : Int
  rank : Int
  balance : 3 * internal + surplus + boundary = 2 * total
  rank_eq : rank = total - internal - boundary + 1
  baseline : P.Ambient -> Prop
  state : P.Ambient
  state_baseline : baseline state

def repairedInternal (component : Component P) : Int :=
  component.boundary - 2 + 2 * component.rank - component.surplus

theorem repairedInternal_eq (component : Component P) :
    component.internal = repairedInternal component := by
  unfold repairedInternal
  exact Core.AffineBalance.solve_one_three
    component.balance component.rank_eq

end Hypostructure.PDE.OneThreeRepair
