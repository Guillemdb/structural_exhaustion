import Mathlib.Tactic
import StructuralExhaustion.Core.Enumeration

namespace StructuralExhaustion.Core.FiniteReceiverDischarge

open scoped BigOperators

universe u

/-!
# Finite receiver discharging

This is the reusable arithmetic core of the Type A `3/7/11` argument.  A
finite support has a degree coordinate at most three.  Degree-three members
are routed to members of degree at most two.  If every receiver's fibre has
size at most `4(3-d)-1`, the exact quarter-charge sum is nonnegative.

The theorem scans only the declared support and routing fibres.  It performs
no graph, path, subset, or routing-function enumeration.
-/

structure Input (Vertex : Type u) where
  vertices : FinEnum Vertex
  support : Finset Vertex
  degree : Vertex → Nat
  degree_le_three : ∀ vertex ∈ support, degree vertex ≤ 3

namespace Input

variable {Vertex : Type u} (input : Input Vertex)

def cubicSet : Finset Vertex := by
  letI : DecidableEq Vertex := input.vertices.decEq
  exact input.support.filter fun vertex => input.degree vertex = 3

def receiverSet : Finset Vertex := by
  letI : DecidableEq Vertex := input.vertices.decEq
  exact input.support.filter fun vertex => input.degree vertex ≤ 2

@[simp]
theorem mem_cubicSet_iff (vertex : Vertex) :
    vertex ∈ input.cubicSet ↔
      vertex ∈ input.support ∧ input.degree vertex = 3 := by
  letI : DecidableEq Vertex := input.vertices.decEq
  simp [cubicSet]

@[simp]
theorem mem_receiverSet_iff (vertex : Vertex) :
    vertex ∈ input.receiverSet ↔
      vertex ∈ input.support ∧ input.degree vertex ≤ 2 := by
  letI : DecidableEq Vertex := input.vertices.decEq
  simp [receiverSet]

theorem cubic_disjoint_receivers :
    Disjoint input.cubicSet input.receiverSet := by
  letI : DecidableEq Vertex := input.vertices.decEq
  rw [Finset.disjoint_left]
  intro vertex cubic receiver
  have cubicDegree := (input.mem_cubicSet_iff vertex).1 cubic
  have receiverDegree := (input.mem_receiverSet_iff vertex).1 receiver
  omega

def partitionSet : Finset Vertex := by
  letI : DecidableEq Vertex := input.vertices.decEq
  exact input.cubicSet ∪ input.receiverSet

theorem support_eq_partitionSet :
    input.support = input.partitionSet := by
  letI : DecidableEq Vertex := input.vertices.decEq
  unfold partitionSet
  ext vertex
  constructor
  · intro member
    have degreeLe := input.degree_le_three vertex member
    by_cases cubic : input.degree vertex = 3
    · exact Finset.mem_union_left _
        ((input.mem_cubicSet_iff vertex).2 ⟨member, cubic⟩)
    · have receiver : input.degree vertex ≤ 2 := by omega
      exact Finset.mem_union_right _
        ((input.mem_receiverSet_iff vertex).2 ⟨member, receiver⟩)
  · intro member
    rcases Finset.mem_union.mp member with cubic | receiver
    · exact (input.mem_cubicSet_iff vertex).1 cubic |>.1
    · exact (input.mem_receiverSet_iff vertex).1 receiver |>.1

def quarterCharge (vertex : Vertex) : Int :=
  4 * ((3 - input.degree vertex : Nat) : Int) - 1

end Input

structure Routing {Vertex : Type u} (input : Input Vertex) where
  route : {vertex // vertex ∈ input.cubicSet} →
    {vertex // vertex ∈ input.receiverSet}

namespace Routing

variable {Vertex : Type u} {input : Input Vertex}
  (routing : Routing input)

noncomputable def routeVertex (vertex : Vertex) : Vertex := by
  letI : DecidableEq Vertex := input.vertices.decEq
  by_cases cubic : vertex ∈ input.cubicSet
  · exact (routing.route ⟨vertex, cubic⟩).1
  · exact vertex

noncomputable def loadSet (receiver : Vertex) : Finset Vertex := by
  letI : DecidableEq Vertex := input.vertices.decEq
  exact input.cubicSet.filter fun cubic =>
    routing.routeVertex cubic = receiver

noncomputable def load (receiver : Vertex) : Nat :=
  (routing.loadSet receiver).card

/-- Excess routed cubic load above the exact `3/7/11` capacity of one
receiver.  This is zero at an unsaturated receiver and records the literal
amount of the Type A continuation at an overloaded receiver. -/
noncomputable def overloadAt (receiver : Vertex) : Nat :=
  routing.load receiver - (4 * (3 - input.degree receiver) - 1)

/-- Total receiver overload on the supplied routing.  The sum ranges only
over the declared receiver set; no routing-function space is searched. -/
noncomputable def totalOverload : Nat :=
  ∑ receiver ∈ input.receiverSet, routing.overloadAt receiver

@[simp]
theorem mem_loadSet_iff (receiver vertex : Vertex) :
    vertex ∈ routing.loadSet receiver ↔
      vertex ∈ input.cubicSet ∧
        routing.routeVertex vertex = receiver := by
  letI : DecidableEq Vertex := input.vertices.decEq
  simp [loadSet]

theorem routeVertex_mem_receiverSet {vertex : Vertex}
    (cubic : vertex ∈ input.cubicSet) :
    routing.routeVertex vertex ∈ input.receiverSet := by
  letI : DecidableEq Vertex := input.vertices.decEq
  simp [routeVertex, cubic]

theorem cubic_card_eq_sum_load :
    input.cubicSet.card =
      ∑ receiver ∈ input.receiverSet, routing.load receiver := by
  letI : DecidableEq Vertex := input.vertices.decEq
  exact Finset.card_eq_sum_card_fiberwise
    (f := routing.routeVertex) (s := input.cubicSet)
    (t := input.receiverSet)
    (fun _vertex cubic => routing.routeVertex_mem_receiverSet cubic)

theorem load_le_capacity_add_overloadAt
    (receiver : Vertex) (member : receiver ∈ input.receiverSet) :
    routing.load receiver ≤
      (4 * (3 - input.degree receiver) - 1) +
        routing.overloadAt receiver := by
  have degree := (input.mem_receiverSet_iff receiver).1 member |>.2
  unfold overloadAt
  omega

/-- The number of cubic vertices is bounded by total receiver capacity plus
the exact overload remainder. -/
theorem cubic_card_le_total_capacity_add_overload :
    input.cubicSet.card ≤
      (∑ receiver ∈ input.receiverSet,
        (4 * (3 - input.degree receiver) - 1)) +
          routing.totalOverload := by
  rw [routing.cubic_card_eq_sum_load]
  calc
    (∑ receiver ∈ input.receiverSet, routing.load receiver) ≤
        ∑ receiver ∈ input.receiverSet,
          ((4 * (3 - input.degree receiver) - 1) +
            routing.overloadAt receiver) :=
      Finset.sum_le_sum fun receiver member =>
        routing.load_le_capacity_add_overloadAt receiver member
    _ = (∑ receiver ∈ input.receiverSet,
          (4 * (3 - input.degree receiver) - 1)) +
        routing.totalOverload := by
      rw [Finset.sum_add_distrib]
      rfl

def Unsaturated : Prop :=
  ∀ receiver ∈ input.receiverSet,
    routing.load receiver ≤ 4 * (3 - input.degree receiver) - 1

theorem overloadAt_eq_zero_of_unsaturated
    (unsaturated : routing.Unsaturated)
    (receiver : Vertex) (member : receiver ∈ input.receiverSet) :
    routing.overloadAt receiver = 0 := by
  have bound := unsaturated receiver member
  unfold overloadAt
  omega

theorem totalOverload_eq_zero_of_unsaturated
    (unsaturated : routing.Unsaturated) :
    routing.totalOverload = 0 := by
  unfold totalOverload
  exact Finset.sum_eq_zero fun receiver member =>
    routing.overloadAt_eq_zero_of_unsaturated unsaturated receiver member

/-- Literal receiver witnessing failure of the `3/7/11` capacity bound. -/
structure Saturated : Type u where
  receiver : Vertex
  receiver_mem : receiver ∈ input.receiverSet
  capacity_lt_load :
    4 * (3 - input.degree receiver) - 1 < routing.load receiver

namespace Saturated

variable (saturated : routing.Saturated)

theorem receiver_degree_le_two :
    input.degree saturated.receiver ≤ 2 :=
  (input.mem_receiverSet_iff saturated.receiver).1
    saturated.receiver_mem |>.2

theorem threshold_le_load :
    4 * (3 - input.degree saturated.receiver) ≤
      routing.load saturated.receiver := by
  have degree := saturated.receiver_degree_le_two
  have overloaded := saturated.capacity_lt_load
  omega

end Saturated

theorem saturated_or_unsaturated :
    Nonempty routing.Saturated ∨ routing.Unsaturated := by
  by_cases unsaturated : routing.Unsaturated
  · exact Or.inr unsaturated
  · left
    unfold Unsaturated at unsaturated
    push Not at unsaturated
    rcases unsaturated with ⟨receiver, member, overloaded⟩
    exact ⟨⟨receiver, member, overloaded⟩⟩

theorem not_unsaturated_iff_nonempty_saturated :
    ¬routing.Unsaturated ↔ Nonempty routing.Saturated := by
  constructor
  · intro notUnsaturated
    rcases routing.saturated_or_unsaturated with saturated | unsaturated
    · exact saturated
    · exact False.elim (notUnsaturated unsaturated)
  · intro saturated unsaturated
    rcases saturated with ⟨saturated⟩
    have bound := unsaturated saturated.receiver saturated.receiver_mem
    exact (Nat.not_lt_of_ge bound) saturated.capacity_lt_load

theorem cubic_charge_eq_neg_card :
    (∑ cubic ∈ input.cubicSet, input.quarterCharge cubic) =
      -(input.cubicSet.card : Int) := by
  calc
    (∑ cubic ∈ input.cubicSet, input.quarterCharge cubic) =
        ∑ _cubic ∈ input.cubicSet, (-1 : Int) := by
      apply Finset.sum_congr rfl
      intro cubic member
      have degree := (input.mem_cubicSet_iff cubic).1 member |>.2
      simp [Input.quarterCharge, degree]
    _ = -(input.cubicSet.card : Int) := by simp

theorem receiver_charge_eq_capacity :
    (∑ receiver ∈ input.receiverSet, input.quarterCharge receiver) =
      ∑ receiver ∈ input.receiverSet,
        ((4 * (3 - input.degree receiver) - 1 : Nat) : Int) := by
  apply Finset.sum_congr rfl
  intro receiver member
  have degree := (input.mem_receiverSet_iff receiver).1 member |>.2
  have positive : 1 ≤ 4 * (3 - input.degree receiver) := by omega
  unfold Input.quarterCharge
  rw [Nat.cast_sub positive]
  norm_num

/-- Exact `3/7/11` receiver discharge in quarter units. -/
theorem quarterCharge_nonnegative (unsaturated : routing.Unsaturated) :
    0 ≤ ∑ vertex ∈ input.support, input.quarterCharge vertex := by
  letI : DecidableEq Vertex := input.vertices.decEq
  have fibreBound :
      ∑ receiver ∈ input.receiverSet, routing.load receiver ≤
        ∑ receiver ∈ input.receiverSet,
          (4 * (3 - input.degree receiver) - 1 : Nat) := by
    exact Finset.sum_le_sum fun receiver member =>
      unsaturated receiver member
  rw [← routing.cubic_card_eq_sum_load] at fibreBound
  have fibreBoundInt :
      (input.cubicSet.card : Int) ≤
        ∑ receiver ∈ input.receiverSet,
          ((4 * (3 - input.degree receiver) - 1 : Nat) : Int) := by
    exact_mod_cast fibreBound
  rw [input.support_eq_partitionSet]
  unfold Input.partitionSet
  rw [Finset.sum_union input.cubic_disjoint_receivers]
  rw [cubic_charge_eq_neg_card (input := input),
    receiver_charge_eq_capacity (input := input)]
  omega

/-- Unconditional quantitative form of the receiver discharge.  Any
negative quarter-charge is bounded by the literal total overload of the
chosen receiver fibres.  The usual unsaturated theorem is the zero-overload
special case. -/
theorem neg_quarterCharge_le_totalOverload :
    -(∑ vertex ∈ input.support, input.quarterCharge vertex) ≤
      (routing.totalOverload : Int) := by
  letI : DecidableEq Vertex := input.vertices.decEq
  have natural := routing.cubic_card_le_total_capacity_add_overload
  have castBound :
      (input.cubicSet.card : Int) ≤
        (∑ receiver ∈ input.receiverSet,
          ((4 * (3 - input.degree receiver) - 1 : Nat) : Int)) +
            (routing.totalOverload : Int) := by
    exact_mod_cast natural
  rw [input.support_eq_partitionSet]
  unfold Input.partitionSet
  rw [Finset.sum_union input.cubic_disjoint_receivers]
  rw [cubic_charge_eq_neg_card (input := input),
    receiver_charge_eq_capacity (input := input)]
  omega

end Routing

end StructuralExhaustion.Core.FiniteReceiverDischarge
