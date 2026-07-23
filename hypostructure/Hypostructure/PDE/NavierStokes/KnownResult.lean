import Hypostructure.PDE.NavierStokes.Runner

/-!
# An unconditional Stokes pipeline fixture

This is deliberately an elementary endpoint: the registered baseline already
contains a classical representative, and the pipeline transports that exact
baseline predicate unchanged.  It validates the full Core strategy boundary
without presenting the fixture as a new Navier--Stokes regularity theorem.
-/

namespace Hypostructure.PDE.NavierStokes.Runner

open Hypostructure
open Hypostructure.PDE.NavierStokes

def representedTarget : Core.Target problem where
  Predicate := RepresentedSolution
  Statement := ∀ field, RepresentedSolution field → RepresentedSolution field
  statement_to_target := by
    intro statement field baseline
    exact statement field baseline
  target_to_statement := by
    intro target
    exact target

def knownStokesProgram : Core.Strategy.TargetProgram problem representedTarget where
  Stage := Core.Strategy.InitStage problem
  branchState := fun _ => ()
  run := (Core.Strategy.InitStrategy.forProblem problem).run
  object_preserved := by
    intro input
    exact Core.Strategy.InitStrategy.run_object problem input
  target := by
    intro input
    change RepresentedSolution input.object
    exact input.baseline

def knownStokesRunner : Core.Strategy.Hypostructure where
  Problem := problem
  Target := representedTarget
  strategy := knownStokesProgram.toOutputStrategy

theorem unconditional_stokes : representedTarget.Statement :=
  knownStokesRunner.unconditional (by
    intro input
    exact ⟨⟨knownStokesProgram.target input⟩, rfl⟩)

end Hypostructure.PDE.NavierStokes.Runner
