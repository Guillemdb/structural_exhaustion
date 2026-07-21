import Hypostructure.Core.Context
import Hypostructure.Core.Residual.Ledger
import HypostructureErdos64EG.Problem

namespace HypostructureErdos64EG

open Hypostructure

universe u

/-!
# Root residual

This is the unique application root. It carries the packed official graph and
its minimum-degree hypothesis, with no target-avoidance, asymptotic, or later
classification data.
-/

/-- The exact graph and hypothesis supplied at the theorem root. -/
structure InitialResidual where
  object : Graph.FiniteObject.{u}
  baseline : problem.Baseline object

namespace InitialResidual

/-- Install the problem's unique initial branch state. -/
def toBranchContext (residual : InitialResidual.{u}) :
    Core.BranchContext problem where
  G := residual.object
  baseline := residual.baseline
  state := ()

end InitialResidual

/-- The unique root stage of the accumulated Hypostructure ledger. -/
abbrev InitialStage := Core.Residual.Ledger InitialResidual.{u}

/-- Seed the framework ledger without adding any premise to the residual. -/
def initialStage (residual : InitialResidual.{u}) : InitialStage.{u} :=
  Core.Residual.Ledger.initial residual

@[simp]
theorem initialStage_residual (residual : InitialResidual.{u}) :
    Core.Residual.residualOf (initialStage residual) = residual :=
  rfl

end HypostructureErdos64EG
