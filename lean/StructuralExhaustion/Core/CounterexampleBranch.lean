import StructuralExhaustion.Core.Problem
import StructuralExhaustion.Core.ResidualRefinement

namespace StructuralExhaustion.Core

universe uAmbient uBranch

/-!
# Initial counterexample branch

The first proof split for a problem is purely logical.  An object is a
counterexample exactly when it satisfies the baseline and avoids the target.
The complementary branch therefore proves the target implication required by
the public theorem.  This layer performs no search.
-/

/-- The exact counterexample predicate attached to a structural-exhaustion
problem and target. -/
def IsCounterexample (P : Problem.{uAmbient, uBranch})
    (Target : P.Ambient → Prop) (G : P.Ambient) : Prop :=
  P.Baseline G ∧ ¬Target G

/-- The negative branch of the counterexample test closes the theorem for the
selected object. -/
theorem target_of_not_isCounterexample
    {P : Problem.{uAmbient, uBranch}} {Target : P.Ambient → Prop}
    {G : P.Ambient} (notCounterexample : ¬IsCounterexample P Target G)
    (baseline : P.Baseline G) : Target G := by
  exact Classical.byContradiction fun avoids =>
    notCounterexample ⟨baseline, avoids⟩

/-- Exact logical characterization of the closed branch. -/
theorem not_isCounterexample_iff
    {P : Problem.{uAmbient, uBranch}} {Target : P.Ambient → Prop}
    {G : P.Ambient} :
    ¬IsCounterexample P Target G ↔ (P.Baseline G → Target G) := by
  constructor
  · intro notCounterexample baseline
    exact target_of_not_isCounterexample notCounterexample baseline
  · intro closes counterexample
    exact counterexample.2 (closes counterexample.1)

/-! ## Accumulated node executor

The first manuscript diamond is common to every structural-exhaustion proof.
The executor below owns its decision and its negative terminal, so examples do
not construct branch sums or transport the initial residual themselves.
-/

namespace CounterexampleBranch

open ResidualRefinement

variable {Residual : Type*}
variable {P : Problem.{uAmbient, uBranch}}
variable {Target : P.Ambient → Prop}

/-- The positive and negative predicates of the initial counterexample
decision, stated on an arbitrary stable residual carrying one ambient object. -/
abbrev Yes (object : Residual → P.Ambient) (residual : Residual) : Prop :=
  IsCounterexample P Target (object residual)

abbrev No (object : Residual → P.Ambient) (residual : Residual) : Prop :=
  ¬IsCounterexample P Target (object residual)

/-- Framework-owned exhaustive counterexample decision. -/
noncomputable def decision
    (object : Residual → P.Ambient) {facts : List (Residual → Prop)} :
    ResidualRefinement.State.DecisionNode (facts := facts)
      (Yes (P := P) (Target := Target) object)
      (No (P := P) (Target := Target) object) :=
  ResidualRefinement.State.DecisionNode.complement _ fun _state =>
    Classical.propDecidable _

/-- The exact negative branch terminal: the retained baseline and the literal
negative decision proof imply the target on the same residual. -/
abbrev Closed (object : Residual → P.Ambient) (residual : Residual) : Prop :=
  Target (object residual)

/-- Execute the initial paper diamond and close only its negative edge.  The
positive edge retains the counterexample proof; the negative edge retains both
its branch proof and the target conclusion. -/
noncomputable def run
    (object : Residual → P.Ambient)
    (baseline : ∀ residual, P.Baseline (object residual))
    {facts : List (Residual → Prop)}
    (state : ResidualRefinement.State Residual facts) :
    ResidualRefinement.State.BranchResult state
      (Yes (P := P) (Target := Target) object :: facts)
      (Closed (Target := Target) object ::
        No (P := P) (Target := Target) object :: facts) :=
  (decision (P := P) (Target := Target) object).run state |>.mapNo
      (property := Closed (Target := Target) object) fun branch =>
    target_of_not_isCounterexample branch.state.latest
      (baseline branch.state.residual)

end CounterexampleBranch

end StructuralExhaustion.Core
