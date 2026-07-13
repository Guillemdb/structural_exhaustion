import StructuralExhaustion.CT2.Observable

namespace StructuralExhaustion.CT2

universe uAmbient uBranch

namespace Observable

/-- The exact reference observation of an ambient object. -/
def observe {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop} (observable : Observable P Target)
    (G : P.Ambient) : Core.ExactObservation :=
  Core.ExactObservation.ofPredicates (P.Baseline G) (Target G)
    (observable.baselineDecidable G) (observable.targetDecidable G)

theorem observe_baseline_true_iff {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop} (observable : Observable P Target)
    (G : P.Ambient) :
    (observable.observe G).baseline = true ↔ P.Baseline G :=
  Core.ExactObservation.baseline_eq_true_iff _ _ _ _

theorem observe_target_true_iff {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop} (observable : Observable P Target)
    (G : P.Ambient) :
    (observable.observe G).target = true ↔ Target G :=
  Core.ExactObservation.target_eq_true_iff _ _ _ _

theorem observe_target_false_iff {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop} (observable : Observable P Target)
    (G : P.Ambient) :
    (observable.observe G).target = false ↔ ¬ Target G := by
  exact Core.truthValue_eq_false_iff _ _

/-- Equality of exact observations transports baseline truth. -/
theorem baseline_of_observation_eq {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop} (observable : Observable P Target)
    {left right : P.Ambient} (same : observable.observe left = observable.observe right)
    (baseline : P.Baseline left) : P.Baseline right := by
  apply (observable.observe_baseline_true_iff right).mp
  rw [← same]
  exact (observable.observe_baseline_true_iff left).mpr baseline

/-- Equality of exact observations transports target avoidance. -/
theorem avoids_of_observation_eq {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop} (observable : Observable P Target)
    {left right : P.Ambient} (same : observable.observe left = observable.observe right)
    (avoids : ¬ Target left) : ¬ Target right := by
  apply (observable.observe_target_false_iff right).mp
  rw [← same]
  exact (observable.observe_target_false_iff left).mpr avoids

end Observable

end StructuralExhaustion.CT2
