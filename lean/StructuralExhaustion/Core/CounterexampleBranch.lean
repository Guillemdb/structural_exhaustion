import StructuralExhaustion.Core.Problem

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

end StructuralExhaustion.Core
