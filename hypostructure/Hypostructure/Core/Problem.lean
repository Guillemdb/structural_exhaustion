import Hypostructure.Core.Prelude

/-!
# Problem kernel

The universal problem data contains only an ambient type, its baseline
predicate, and the branch state indexed by the current ambient object. Targets
and optional capabilities are supplied separately.
-/

namespace Hypostructure.Core

universe uAmbient uBranch

/-- Irreducible data shared by every tactic in one proof program. -/
structure Problem where
  Ambient : Type uAmbient
  Baseline : Ambient -> Prop
  BranchState : Ambient -> Type uBranch

/-! ## Target boundary

Targets are kept separate from `Problem` so the same problem registration can
be reused by different theorem statements or terminal predicates.  The two
bridge fields are formulation laws, not a proof of the statement itself.
-/

structure Target (P : Problem) where
  Predicate : P.Ambient -> Prop
  Statement : Prop
  statement_to_target :
    Statement -> forall object, P.Baseline object -> Predicate object
  target_to_statement :
    (forall object, P.Baseline object -> Predicate object) -> Statement

/-- Complete theorem registration consumed by the strategy DAG runner.  The
application exposes one value containing both its ambient problem and target;
execution concerns are deliberately absent. -/
structure ProblemDefinition where
  problem : Problem.{uAmbient, uBranch}
  target : Target problem
  initialState : forall object, problem.BranchState object

end Hypostructure.Core
