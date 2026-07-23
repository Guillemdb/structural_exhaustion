import Hypostructure.Core.Strategy.Dag

namespace Template

open Hypostructure

universe uAmbient uBranch uStage

/-!
# Problem definition template

A concrete application replaces the parameters in this section with its
registered problem, target, and Core-composed strategy.  The only exported
entry point required by the runner is `problemDefinition`.
-/

section ProblemDefinition

variable (problem : Core.ProblemDefinition)
variable (dag : Core.Strategy.Dag.Blueprint
  (Core.Strategy.ProblemInput problem.problem))

noncomputable def problemDefinition : Core.Strategy.Dag.ProblemDeclaration :=
  Core.Strategy.Dag.ProblemDeclaration.ofDag problem dag

-- Core owns runner construction and output diagnostics.
#check problemDefinition
#check Core.Strategy.Dag.ProblemDeclaration.run
#check Core.Strategy.Dag.ProblemDeclaration.diagnose
#check Core.Strategy.Dag.ProblemDeclaration.result
#check Core.Strategy.Dag.ProblemDeclaration.report
#check Core.Strategy.Dag.ProblemDeclaration.unconditional

end ProblemDefinition

end Template
