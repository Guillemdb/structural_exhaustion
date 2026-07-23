import Hypostructure.Core.Strategy.Dag
import HypostructureErdos64EG.Problem

/-!
# First executable EG strategy

The root ledger is followed by one framework target-or-avoidance strategy.
The application supplies no route, ledger extension, output strategy, or
result: Core owns composition and finalization.
-/

namespace HypostructureErdos64EG.FirstStrategyDag

open Hypostructure
open Hypostructure.Core.Residual

abbrev RootStage :=
  Core.Strategy.InitStage HypostructureErdos64EG.problem

/-- The first strategy performs the exhaustive target/continuation split on
the literal graph stored in the root residual. -/
noncomputable def firstStrategy :
    Core.Strategy.TargetAvoidingContinuation RootStage where
  TargetCertificate previous :=
    PUnit
  AvoidingResidual _previous := PUnit
  target previous _certificate :=
    HypostructureErdos64EG.Target (residualOf previous).object
  avoiding _previous := PUnit.unit
  target_or_avoiding previous := by
    classical
    by_cases target :
        HypostructureErdos64EG.Target (residualOf previous).object
    · exact Or.inl ⟨PUnit.unit, target⟩
    · exact Or.inr ⟨PUnit.unit⟩

/-- Minimal executable DAG: framework initialization followed by one
registered strategy vertex. -/
noncomputable def strategyDag :
    Core.Strategy.Dag.Blueprint
      (Core.Strategy.ProblemInput HypostructureErdos64EG.problem) :=
  Core.Strategy.Dag.Blueprint.root.add
    (Core.Strategy.Dag.Registered.targetAvoiding firstStrategy)

/-- Core-owned compilation and execution boundary. -/
noncomputable def problemDefinition :
    Core.Strategy.Dag.ProblemDeclaration :=
  Core.Strategy.Dag.ProblemDeclaration.ofDag
    HypostructureErdos64EG.definition strategyDag

/-- Kernel-certified total result of the one-strategy DAG. -/
theorem strategyResult : problemDefinition.Result :=
  problemDefinition.result

#check problemDefinition.report
#print axioms strategyResult

end HypostructureErdos64EG.FirstStrategyDag
