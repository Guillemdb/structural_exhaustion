import Hypostructure.Core.Strategy
import Hypostructure.PDE.NavierStokes.Basic

/-!
# Core-only Stokes pressure strategy

This fixture uses the framework directly.  The strategy constructs a local
pressure row and a global/harmonic remainder row, then closes by exact
reconstruction.  No decomposition is supplied in the problem baseline.
-/

namespace Hypostructure.Fixtures.StokesCore

open Hypostructure
open Hypostructure.PDE.NavierStokes

structure PressureDecomposition (field : Field) where
  localPart : Spacetime → Real
  globalPart : Spacetime → Real
  pressure : Spacetime → Real
  pressure_eq : pressure = field.pressure
  reconstruct : ∀ z, localPart z + globalPart z = pressure z

def problem : Core.Problem where
  Ambient := Field
  Baseline := fun _ => True
  BranchState := fun _ => Unit

def target : Core.Target problem where
  Predicate := fun field => Nonempty (PressureDecomposition field)
  Statement := ∀ field, Nonempty (PressureDecomposition field)
  statement_to_target := by
    intro statement field _baseline
    exact statement field
  target_to_statement := by
    intro target field
    exact target field trivial

inductive Row
  | localPressure
  | globalPressure
  | reconstructed
deriving DecidableEq

structure PipelineState where
  field : Field
  row : Row
  split : PressureDecomposition field

def runState (input : Core.Strategy.ProblemInput problem) : PipelineState := {
  field := input.object
  row := .reconstructed
  split := {
    localPart := input.object.pressure
    globalPart := fun _ => 0
    pressure := input.object.pressure
    pressure_eq := rfl
    reconstruct := by intro z; simp
  }
}

instance : Core.Residual.HasResidual PipelineState (Core.Strategy.ProblemInput problem) where
  residual state := {
    object := state.field
    baseline := trivial
    branchState := ()
  }

def pressurePipeline : Core.Strategy.TargetProgram problem target where
  Stage := PipelineState
  branchState := fun _ => ()
  run := runState
  object_preserved := by
    intro input
    rfl
  target := by
    intro input
    let state := runState input
    exact ⟨state.split⟩

def runner : Core.Strategy.Hypostructure where
  Problem := problem
  Target := target
  strategy := pressurePipeline.toOutputStrategy

theorem unconditional_pressure_reconstruction : target.Statement :=
  runner.unconditional (by
    intro input
    exact ⟨⟨pressurePipeline.target input⟩, rfl⟩)

end Hypostructure.Fixtures.StokesCore
