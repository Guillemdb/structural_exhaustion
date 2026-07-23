import Hypostructure.Core.Strategy.Dag
import HypostructureErdos64EG.Problem

/-!
# Strategy DAG execution

The application supplies only its registered problem and a framework-built
DAG.  Core compiles and executes the DAG and proves its target-or-residual
result.  No node, route, payload, or outcome is defined here.
-/

namespace HypostructureErdos64EG

open Hypostructure

def strategyDag :
    Core.Strategy.Dag.Blueprint (Core.Strategy.ProblemInput problem) :=
  Core.Strategy.Dag.Blueprint.root

noncomputable def problemDefinition :
    Core.Strategy.Dag.ProblemDeclaration :=
  Core.Strategy.Dag.ProblemDeclaration.ofDag definition strategyDag

#check problemDefinition.report

end HypostructureErdos64EG
