import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.Walk.Counting
import StructuralExhaustion.Core.Enumeration

namespace StructuralExhaustion.Graph.FinitePathCertificateWork

universe u v

/-!
# Work accounting for supplied finite path certificates

These definitions count a single pass over an explicitly supplied schedule
and the supports of paths already carried by certificates.  They never search
for a walk, graph, or context.
-/

/-- The edge length of a supplied simple path is bounded by the declared host
vertex universe. -/
theorem pathLength_le_vertices {V : Type u} (vertices : FinEnum V)
    {G : SimpleGraph V} {start finish : V} (path : G.Walk start finish)
    (isPath : path.IsPath) :
    path.length ≤ vertices.card := by
  letI : FinEnum V := vertices
  letI : Fintype V := @FinEnum.instFintype V vertices
  have supportBound : path.support.length ≤ vertices.card := by
    simpa [FinEnum.card_eq_fintypeCard] using
      isPath.support_nodup.length_le_card
  rw [SimpleGraph.Walk.length_support] at supportBound
  omega

/-- One constant descriptor check plus the declared certificate cost at each
actually scheduled item. -/
def scheduledChecks {A : Type v} (schedule : List A) (cost : A → Nat) : Nat :=
  (schedule.map fun item ↦ cost item + 1).sum

/-- A pointwise certificate bound lifts to a bound for the single scheduled
pass. -/
theorem scheduledChecks_le {A : Type v} (schedule : List A) (cost : A → Nat)
    (cap : Nat) (costLe : ∀ item ∈ schedule, cost item ≤ cap) :
    scheduledChecks schedule cost ≤ schedule.length * (cap + 1) := by
  induction schedule with
  | nil => simp [scheduledChecks]
  | cons head tail ih =>
      have headLe : cost head ≤ cap := costLe head (by simp)
      have tailLe : ∀ item ∈ tail, cost item ≤ cap := by
        intro item member
        exact costLe item (by simp [member])
      have tailBound := ih tailLe
      change cost head + 1 + scheduledChecks tail cost ≤
        (tail.length + 1) * (cap + 1)
      calc
        cost head + 1 + scheduledChecks tail cost ≤
            (cap + 1) + tail.length * (cap + 1) :=
          Nat.add_le_add (Nat.add_le_add_right headLe 1) tailBound
        _ = (tail.length + 1) * (cap + 1) := by ring

/-- The same accounting when only an upper bound for schedule length is
exposed by the producer. -/
theorem scheduledChecks_le_of_length_le {A : Type v} (schedule : List A)
    (cost : A → Nat) (cap slots : Nat)
    (costLe : ∀ item ∈ schedule, cost item ≤ cap)
    (lengthLe : schedule.length ≤ slots) :
    scheduledChecks schedule cost ≤ slots * (cap + 1) := by
  exact (scheduledChecks_le schedule cost cap costLe).trans
    (Nat.mul_le_mul_right (cap + 1) lengthLe)

end StructuralExhaustion.Graph.FinitePathCertificateWork
