import StructuralExhaustion.Core.FinitePrefixExtensionFamily

namespace StructuralExhaustion.Examples.FinitePrefixExtensionFamily

open StructuralExhaustion.Core
open FinitePrefixExtension

def windows : List (Fin 3) := [0, 1, 2]

def coordinates (_ : Fin 3) : List (Fin 2) := [0, 1]

def pointwiseMachine (window : Fin 3) : Machine (Fin 2) where
  State := fun _ => Unit
  Failure := fun _ => Fin 3
  root := ()
  extend := fun _ _ =>
    if window = 1 then .obstructed window else .extended ()

def firstFailure :
    FinitePrefixExtensionFamily.FirstObstruction pointwiseMachine coordinates
      windows := by
  apply FinitePrefixExtensionFamily.FirstObstruction.later
  · apply Complete.cons () (by simp [pointwiseMachine])
    apply Complete.cons () (by simp [pointwiseMachine])
    exact Complete.nil (machine := pointwiseMachine 0) ()
  · apply FinitePrefixExtensionFamily.FirstObstruction.here
    apply FinitePrefixExtension.FirstObstruction.here (failure := (1 : Fin 3))
    simp [pointwiseMachine]

theorem first_obstruction_is_second_window :
    FinitePrefixExtensionFamily.run pointwiseMachine coordinates windows =
      .firstObstruction firstFailure := by
  simp [FinitePrefixExtensionFamily.run, Machine.run,
    FinitePrefixExtension.runFrom, pointwiseMachine, coordinates, windows,
    firstFailure]

def alwaysExtends (_ : Fin 3) : Machine (Fin 2) where
  State := fun _ => Unit
  Failure := fun _ => Empty
  root := ()
  extend := fun _ _ => .extended ()

theorem every_window_completes :
    ∃ ledgers,
      FinitePrefixExtensionFamily.run alwaysExtends coordinates windows =
        .allComplete ledgers := by
  exact (FinitePrefixExtensionFamily.run_exhaustive
    alwaysExtends coordinates windows).resolve_left (by
      rintro ⟨failure, equation⟩
      simp [FinitePrefixExtensionFamily.run, Machine.run,
        FinitePrefixExtension.runFrom, alwaysExtends, coordinates, windows]
        at equation)

example :
    FinitePrefixExtensionFamily.visibleCheckEnvelope coordinates windows = 6 := rfl

end StructuralExhaustion.Examples.FinitePrefixExtensionFamily
