import Mathlib.Tactic
import StructuralExhaustion.Graph.AssignedSupportCharge

namespace StructuralExhaustion.Graph.PositiveDeficiencyWedge

open StructuralExhaustion
open scoped BigOperators

universe u

/-!
# Positive deficiency, boundary incidences, and length-two wedges

This profile is the graph-generic finite accounting kernel used by the
remainder-curvature stage.  It scans one supplied vertex set.  In particular,
it neither enumerates connected subgraphs nor constructs a family of graphs.
-/

variable {V : Type u}

structure Profile (object : FiniteObject V) where
  core : Finset V

namespace Profile

variable {object : FiniteObject V} (profile : Profile object)

noncomputable def internalDegree (vertex : V) : Nat := by
  letI : FinEnum V := object.input.vertices
  letI : DecidableEq V := object.input.vertices.decEq
  letI : DecidableRel object.graph.Adj := object.input.decideAdj
  exact (object.graph.neighborFinset vertex ∩ profile.core).card

noncomputable def externalDegree (vertex : V) : Nat := by
  letI : FinEnum V := object.input.vertices
  letI : DecidableEq V := object.input.vertices.decEq
  letI : DecidableRel object.graph.Adj := object.input.decideAdj
  exact (object.graph.neighborFinset vertex \ profile.core).card

noncomputable def positiveDeficiency : Nat :=
  profile.core.sum (fun vertex : V => 3 - internalDegree profile vertex)

noncomputable def boundaryIncidences : Nat :=
  profile.core.sum (fun vertex : V => externalDegree profile vertex)

noncomputable def wedgeCount : Nat :=
  profile.core.sum (fun vertex : V => Nat.choose (internalDegree profile vertex) 2)

theorem internal_add_external_eq_degree (vertex : V) :
    profile.internalDegree vertex + profile.externalDegree vertex =
      object.degree vertex := by
  letI : FinEnum V := object.input.vertices
  letI : DecidableEq V := object.input.vertices.decEq
  letI : DecidableRel object.graph.Adj := object.input.decideAdj
  unfold internalDegree externalDegree FiniteObject.degree
  let neighbors := object.graph.neighborFinset vertex
  have subset : neighbors ∩ profile.core ⊆ neighbors := Finset.inter_subset_left
  have counted := Finset.card_sdiff_add_card_eq_card subset
  have difference : neighbors \ (neighbors ∩ profile.core) =
      neighbors \ profile.core := by
    ext neighbor
    simp
  rw [difference] at counted
  change (neighbors ∩ profile.core).card +
      (neighbors \ profile.core).card = neighbors.card
  rw [Nat.add_comm]
  exact counted

theorem deficiencyAt_le_externalDegree
    (baseline : ∀ vertex, 3 ≤ object.degree vertex) (vertex : V) :
    3 - profile.internalDegree vertex ≤ profile.externalDegree vertex := by
  have degreeEq := profile.internal_add_external_eq_degree vertex
  have minimum := baseline vertex
  omega

/-- Every unit of positive deficiency is paid by an actual incidence leaving
the supplied support. -/
theorem positiveDeficiency_le_boundaryIncidences
    (baseline : ∀ vertex, 3 ≤ object.degree vertex) :
    profile.positiveDeficiency ≤ profile.boundaryIncidences := by
  unfold positiveDeficiency boundaryIncidences
  exact Finset.sum_le_sum fun vertex _member =>
    profile.deficiencyAt_le_externalDegree baseline vertex

private theorem three_le_choose_add_twice_deficit (degree : Nat) :
    3 ≤ Nat.choose degree 2 + 2 * (3 - degree) := by
  by_cases small : degree ≤ 2
  · interval_cases degree <;> decide
  · have three_le_degree : 3 ≤ degree := by omega
    have chooseLower : 3 ≤ Nat.choose degree 2 := by
      simpa using Nat.choose_le_choose 2 three_le_degree
    omega

/-- Exact finite wedge floor.  This is the integer theorem underlying all
normalized or asymptotic versions of the manuscript bound. -/
theorem three_mul_card_le_wedgeCount_add_twice_deficiency :
    3 * profile.core.card ≤
      profile.wedgeCount + 2 * profile.positiveDeficiency := by
  have pointwise : ∀ vertex ∈ profile.core,
      3 ≤ Nat.choose (profile.internalDegree vertex) 2 +
        2 * (3 - profile.internalDegree vertex) := by
    intro vertex _member
    exact three_le_choose_add_twice_deficit _
  have summed := Finset.sum_le_sum pointwise
  simpa [wedgeCount, positiveDeficiency, Finset.sum_add_distrib,
    Finset.mul_sum, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using summed

/-- Framework-owned composition of the exact wedge identity with any already
proved upper bound on positive deficiency.  Applications provide only their
problem-specific supply ceiling; no degree sum is re-expanded downstream. -/
theorem three_mul_card_le_wedgeCount_add_twice_cap {cap : Nat}
    (deficiency_le : profile.positiveDeficiency ≤ cap) :
    3 * profile.core.card ≤ profile.wedgeCount + 2 * cap := by
  calc
    3 * profile.core.card ≤
        profile.wedgeCount + 2 * profile.positiveDeficiency :=
      profile.three_mul_card_le_wedgeCount_add_twice_deficiency
    _ ≤ profile.wedgeCount + 2 * cap :=
      Nat.add_le_add_left (Nat.mul_le_mul_left 2 deficiency_le) _

theorem wedgeFloor :
    3 * profile.core.card - 2 * profile.positiveDeficiency ≤
      profile.wedgeCount := by
  have exactFloor :=
    profile.three_mul_card_le_wedgeCount_add_twice_deficiency
  omega

/-- Real-arithmetic transport of the exact wedge floor.  An application may
supply any proved deficiency-rate estimate and explicit additive error; the
graph layer converts it to the corresponding wedge-rate estimate without
enumerating components or coordinates. -/
theorem wedgeRate_of_deficiencyRate
    (rate error : ℝ)
    (deficiencyRate : (profile.positiveDeficiency : ℝ) ≤
      rate * profile.core.card + error) :
    (3 - 2 * rate) * profile.core.card ≤
      profile.wedgeCount + 2 * error := by
  have floorReal :
      (3 : ℝ) * profile.core.card ≤
        profile.wedgeCount + 2 * profile.positiveDeficiency := by
    exact_mod_cast profile.three_mul_card_le_wedgeCount_add_twice_deficiency
  nlinarith

theorem internalDegree_le_vertexCount (vertex : V) :
    profile.internalDegree vertex ≤ object.input.vertices.card := by
  letI : FinEnum V := object.input.vertices
  letI : DecidableEq V := object.input.vertices.decEq
  letI : DecidableRel object.graph.Adj := object.input.decideAdj
  unfold internalDegree
  calc
    (object.graph.neighborFinset vertex ∩ profile.core).card ≤
        (Finset.univ : Finset V).card :=
      Finset.card_le_univ _
    _ = object.input.vertices.card := by
      simp [FinEnum.card_eq_fintypeCard]

/-- The raw length-two coordinate universe is cubic in the declared ambient
vertex count.  It is computed by one neighbor-pair scan per supplied support
vertex; no support family or graph family is generated. -/
theorem wedgeCount_le_cube :
    profile.wedgeCount ≤ object.input.vertices.card ^ 3 := by
  letI : FinEnum V := object.input.vertices
  have coreBound : profile.core.card ≤ object.input.vertices.card := by
    calc
      profile.core.card ≤ (Finset.univ : Finset V).card :=
        Finset.card_le_univ profile.core
      _ = object.input.vertices.card := by
        simp [FinEnum.card_eq_fintypeCard]
  unfold wedgeCount
  calc
    ∑ vertex ∈ profile.core,
        Nat.choose (profile.internalDegree vertex) 2 ≤
      ∑ _vertex ∈ profile.core, object.input.vertices.card ^ 2 := by
        apply Finset.sum_le_sum
        intro vertex _member
        calc
          Nat.choose (profile.internalDegree vertex) 2 ≤
              profile.internalDegree vertex ^ 2 :=
            Nat.choose_le_pow _ _
          _ ≤ object.input.vertices.card ^ 2 := by
            gcongr
            exact profile.internalDegree_le_vertexCount vertex
    _ = profile.core.card * object.input.vertices.card ^ 2 := by
      simp
    _ ≤ object.input.vertices.card * object.input.vertices.card ^ 2 := by
      exact Nat.mul_le_mul_right _ coreBound
    _ = object.input.vertices.card ^ 3 := by ring

/-- The local implementation uses one neighbour scan per support vertex. -/
noncomputable def checks : Nat :=
  profile.core.card * object.input.vertices.card

theorem checks_le_square :
    profile.checks ≤ object.input.vertices.card ^ 2 := by
  letI : FinEnum V := object.input.vertices
  have coreBound : profile.core.card ≤ object.input.vertices.card := by
    calc
      profile.core.card ≤ (Finset.univ : Finset V).card :=
        Finset.card_le_univ profile.core
      _ = object.input.vertices.card := by
        simp [FinEnum.card_eq_fintypeCard]
  unfold checks
  nlinarith

end Profile

end StructuralExhaustion.Graph.PositiveDeficiencyWedge
