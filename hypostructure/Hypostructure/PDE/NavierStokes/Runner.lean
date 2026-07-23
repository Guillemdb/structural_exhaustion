import Hypostructure.Core.Strategy
import Hypostructure.PDE.NavierStokes.Basic

/-!
# Core Hypostructure runner for two-dimensional Navier--Stokes

This is only the PDE instantiation of Core's runner boundary.  A caller must
provide one composed `Core.Strategy.Chain`; the PDE layer supplies
the regularity target and exposes Core's unconditional theorem-or-residual
projections.  No CT is run here and no analytic theorem is assumed.
-/

namespace Hypostructure.PDE.NavierStokes.Runner

open Hypostructure
open Hypostructure.PDE.NavierStokes

def GlobalRegularity (field : Field) : Prop :=
  ∀ z, z ∈ field.domain ->
    ContDiffAt Real ⊤ field.velocity z

def target : Core.Target problem where
  Predicate := GlobalRegularity
  Statement := ∀ field, RepresentedSolution field -> GlobalRegularity field
  statement_to_target := by
    intro statement field baseline
    exact statement field baseline
  target_to_statement := by
    intro target
    exact target

structure Program where
  strategy : Core.Strategy.Chain problem target

def coreProgram (program : Program) : Core.Strategy.Hypostructure where
  Problem := problem
  Target := target
  strategy := program.strategy

def run (program : Program) :=
  (coreProgram program).run

noncomputable def diagnose (program : Program) :=
  (coreProgram program).diagnose

theorem unconditional
    (program : Program)
    (target_case : ∀ input,
      ∃ proof : PLift (target.Predicate
        (@Core.Residual.residualOf program.strategy.Stage
          (Core.Strategy.ProblemInput problem)
          program.strategy.stageResidual
          (program.strategy.run input).previous).object),
        program.strategy.output input = Sum.inl proof) :
    target.Statement :=
  (coreProgram program).unconditional target_case

noncomputable def unconditionalOrResidual (program : Program) :
    Sum (PLift target.Statement)
      (Sigma fun input =>
        Sigma fun residual : program.strategy.Remaining
            (program.strategy.run input).previous =>
          PLift (program.strategy.output input = Sum.inr residual)) :=
  Core.Strategy.OutputStrategy.closeOrResidual program.strategy

end Hypostructure.PDE.NavierStokes.Runner
