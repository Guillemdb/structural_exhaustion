import StructuralExhaustion.Core.FinitePrefixExtension

namespace StructuralExhaustion.Examples.FinitePrefixExtension

open StructuralExhaustion.Core.FinitePrefixExtension

/-- Four literal coordinates; the third coordinate carries the first
application-produced obstruction. -/
def coordinates : List (Fin 4) := [0, 1, 2, 3]

def obstructAtTwo : Machine (Fin 4) where
  State := fun _ => Unit
  Failure := fun _ => Fin 4
  root := ()
  extend := fun _ coordinate =>
    if coordinate = 2 then .obstructed coordinate else .extended ()

def firstAtTwo : FirstObstruction obstructAtTwo obstructAtTwo.root coordinates :=
  .later () (by simp [obstructAtTwo])
    (.later () (by simp [obstructAtTwo])
      (.here (by change Fin 4; exact 2) (by simp [obstructAtTwo])))

theorem obstructs_at_third_coordinate :
    obstructAtTwo.run coordinates = .firstObstruction firstAtTwo := by
  simp [Machine.run, runFrom, coordinates, obstructAtTwo, firstAtTwo]

theorem obstruction_index_is_two : firstAtTwo.index = 2 := by
  simp [firstAtTwo, FirstObstruction.index]

theorem obstruction_coordinate_is_two : firstAtTwo.coordinate = 2 := by
  simp [firstAtTwo, FirstObstruction.coordinate]

def alwaysExtends : Machine (Fin 4) where
  State := fun _ => Unit
  Failure := fun _ => Empty
  root := ()
  extend := fun _ _ => .extended ()

def completeLedger : Complete alwaysExtends alwaysExtends.root coordinates := by
  refine .cons () (by simp [alwaysExtends]) ?_
  refine .cons () (by simp [alwaysExtends]) ?_
  refine .cons () (by simp [alwaysExtends]) ?_
  refine .cons () (by simp [alwaysExtends]) ?_
  exact Complete.nil (machine := alwaysExtends) ()

theorem complete_schedule :
    alwaysExtends.run coordinates = .complete completeLedger := by
  simp [Machine.run, runFrom, coordinates, alwaysExtends, completeLedger]

example : visibleChecks coordinates = 4 := rfl

end StructuralExhaustion.Examples.FinitePrefixExtension
