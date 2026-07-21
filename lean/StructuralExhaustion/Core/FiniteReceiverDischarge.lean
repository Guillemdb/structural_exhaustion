import Mathlib.Tactic
import StructuralExhaustion.Core.Enumeration

namespace StructuralExhaustion.Core.FiniteReceiverDischarge

open scoped BigOperators

universe u

/-!
# Finite receiver discharging

This is the reusable arithmetic core of finite receiver discharging.  A
finite support has a degree coordinate bounded by a caller-supplied source
degree.  Source-degree members are routed to lower-degree receivers.  If
every receiver's fibre has size at most
`scale * (sourceDegree - d) - 1`, the exact signed charge sum is
nonnegative.

The theorem scans only the declared support and routing fibres.  It performs
no graph, path, subset, or routing-function enumeration.
-/

/-- Numeric parameters for a finite receiver-discharge profile. -/
structure Parameters where
  /-- The degree of the charged source vertices. -/
  sourceDegree : Nat
  /-- Integral normalization of one unit of deficiency. -/
  scale : Nat
  scale_pos : 0 < scale

namespace Parameters

/-- Receiver capacity at a given degree. -/
def capacity (parameters : Parameters) (degree : Nat) : Nat :=
  parameters.scale * (parameters.sourceDegree - degree) - 1

end Parameters

structure Input (Vertex : Type u) where
  parameters : Parameters
  vertices : FinEnum Vertex
  support : Finset Vertex
  degree : Vertex → Nat
  degree_le_source : ∀ vertex ∈ support, degree vertex ≤ parameters.sourceDegree

namespace Input

variable {Vertex : Type u} (input : Input Vertex)

def sourceSet : Finset Vertex := by
  letI : DecidableEq Vertex := input.vertices.decEq
  exact input.support.filter fun vertex =>
    input.degree vertex = input.parameters.sourceDegree

def receiverSet : Finset Vertex := by
  letI : DecidableEq Vertex := input.vertices.decEq
  exact input.support.filter fun vertex =>
    input.degree vertex < input.parameters.sourceDegree

@[simp]
theorem mem_sourceSet_iff (vertex : Vertex) :
    vertex ∈ input.sourceSet ↔
      vertex ∈ input.support ∧
        input.degree vertex = input.parameters.sourceDegree := by
  letI : DecidableEq Vertex := input.vertices.decEq
  simp [sourceSet]

@[simp]
theorem mem_receiverSet_iff (vertex : Vertex) :
    vertex ∈ input.receiverSet ↔
      vertex ∈ input.support ∧
        input.degree vertex < input.parameters.sourceDegree := by
  letI : DecidableEq Vertex := input.vertices.decEq
  simp [receiverSet]

theorem source_disjoint_receivers :
    Disjoint input.sourceSet input.receiverSet := by
  letI : DecidableEq Vertex := input.vertices.decEq
  rw [Finset.disjoint_left]
  intro vertex source receiver
  have sourceDegree := (input.mem_sourceSet_iff vertex).1 source
  have receiverDegree := (input.mem_receiverSet_iff vertex).1 receiver
  omega

def partitionSet : Finset Vertex := by
  letI : DecidableEq Vertex := input.vertices.decEq
  exact input.sourceSet ∪ input.receiverSet

theorem support_eq_partitionSet :
    input.support = input.partitionSet := by
  letI : DecidableEq Vertex := input.vertices.decEq
  unfold partitionSet
  ext vertex
  constructor
  · intro member
    have degreeLe := input.degree_le_source vertex member
    by_cases source : input.degree vertex = input.parameters.sourceDegree
    · exact Finset.mem_union_left _
        ((input.mem_sourceSet_iff vertex).2 ⟨member, source⟩)
    · have receiver : input.degree vertex < input.parameters.sourceDegree := by omega
      exact Finset.mem_union_right _
        ((input.mem_receiverSet_iff vertex).2 ⟨member, receiver⟩)
  · intro member
    rcases Finset.mem_union.mp member with source | receiver
    · exact (input.mem_sourceSet_iff vertex).1 source |>.1
    · exact (input.mem_receiverSet_iff vertex).1 receiver |>.1

def signedCharge (vertex : Vertex) : Int :=
  input.parameters.scale *
    ((input.parameters.sourceDegree - input.degree vertex : Nat) : Int) - 1

def receiverCapacity (vertex : Vertex) : Nat :=
  input.parameters.capacity (input.degree vertex)

end Input

structure Routing {Vertex : Type u} (input : Input Vertex) where
  route : {vertex // vertex ∈ input.sourceSet} →
    {vertex // vertex ∈ input.receiverSet}

namespace Routing

variable {Vertex : Type u} {input : Input Vertex}
  (routing : Routing input)

noncomputable def routeVertex (vertex : Vertex) : Vertex := by
  letI : DecidableEq Vertex := input.vertices.decEq
  by_cases source : vertex ∈ input.sourceSet
  · exact (routing.route ⟨vertex, source⟩).1
  · exact vertex

noncomputable def loadSet (receiver : Vertex) : Finset Vertex := by
  letI : DecidableEq Vertex := input.vertices.decEq
  exact input.sourceSet.filter fun source =>
    routing.routeVertex source = receiver

noncomputable def load (receiver : Vertex) : Nat :=
  (routing.loadSet receiver).card

/-- Excess routed source load above the exact parameterized capacity of one
receiver.  This is zero at an unsaturated receiver and records the literal
amount of the continuation at an overloaded receiver. -/
noncomputable def overloadAt (receiver : Vertex) : Nat :=
  routing.load receiver - input.receiverCapacity receiver

/-- Total receiver overload on the supplied routing.  The sum ranges only
over the declared receiver set; no routing-function space is searched. -/
noncomputable def totalOverload : Nat :=
  ∑ receiver ∈ input.receiverSet, routing.overloadAt receiver

@[simp]
theorem mem_loadSet_iff (receiver vertex : Vertex) :
    vertex ∈ routing.loadSet receiver ↔
      vertex ∈ input.sourceSet ∧
        routing.routeVertex vertex = receiver := by
  letI : DecidableEq Vertex := input.vertices.decEq
  simp [loadSet]

theorem routeVertex_mem_receiverSet {vertex : Vertex}
    (source : vertex ∈ input.sourceSet) :
    routing.routeVertex vertex ∈ input.receiverSet := by
  letI : DecidableEq Vertex := input.vertices.decEq
  simp [routeVertex, source]

theorem source_card_eq_sum_load :
    input.sourceSet.card =
      ∑ receiver ∈ input.receiverSet, routing.load receiver := by
  letI : DecidableEq Vertex := input.vertices.decEq
  exact Finset.card_eq_sum_card_fiberwise
    (f := routing.routeVertex) (s := input.sourceSet)
    (t := input.receiverSet)
    (fun _vertex source => routing.routeVertex_mem_receiverSet source)

theorem load_le_capacity_add_overloadAt
    (receiver : Vertex) (_member : receiver ∈ input.receiverSet) :
    routing.load receiver ≤
      input.receiverCapacity receiver + routing.overloadAt receiver := by
  unfold overloadAt
  omega

/-- The number of source vertices is bounded by total receiver capacity plus
the exact overload remainder. -/
theorem source_card_le_total_capacity_add_overload :
    input.sourceSet.card ≤
      (∑ receiver ∈ input.receiverSet, input.receiverCapacity receiver) +
          routing.totalOverload := by
  rw [routing.source_card_eq_sum_load]
  calc
    (∑ receiver ∈ input.receiverSet, routing.load receiver) ≤
        ∑ receiver ∈ input.receiverSet,
          (input.receiverCapacity receiver + routing.overloadAt receiver) :=
      Finset.sum_le_sum fun receiver member =>
        routing.load_le_capacity_add_overloadAt receiver member
    _ = (∑ receiver ∈ input.receiverSet, input.receiverCapacity receiver) +
        routing.totalOverload := by
      rw [Finset.sum_add_distrib]
      rfl

def Unsaturated : Prop :=
  ∀ receiver ∈ input.receiverSet,
    routing.load receiver ≤ input.receiverCapacity receiver

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

/-- Literal receiver witnessing failure of the capacity bound. -/
structure Saturated : Type u where
  receiver : Vertex
  receiver_mem : receiver ∈ input.receiverSet
  capacity_lt_load :
    input.receiverCapacity receiver < routing.load receiver

namespace Saturated

variable (saturated : routing.Saturated)

theorem receiver_degree_lt_source :
    input.degree saturated.receiver < input.parameters.sourceDegree :=
  (input.mem_receiverSet_iff saturated.receiver).1
    saturated.receiver_mem |>.2

theorem threshold_le_load :
    input.parameters.scale *
        (input.parameters.sourceDegree - input.degree saturated.receiver) ≤
      routing.load saturated.receiver := by
  have degree := saturated.receiver_degree_lt_source
  have overloaded := saturated.capacity_lt_load
  have positive :
      1 ≤ input.parameters.scale *
        (input.parameters.sourceDegree - input.degree saturated.receiver) := by
    have diff_pos :
        0 < input.parameters.sourceDegree - input.degree saturated.receiver := by
      omega
    have product_pos :
        0 < input.parameters.scale *
          (input.parameters.sourceDegree - input.degree saturated.receiver) :=
      Nat.mul_pos input.parameters.scale_pos diff_pos
    omega
  unfold Input.receiverCapacity Parameters.capacity at overloaded
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

theorem source_charge_eq_neg_card :
    (∑ source ∈ input.sourceSet, input.signedCharge source) =
      -(input.sourceSet.card : Int) := by
  calc
    (∑ source ∈ input.sourceSet, input.signedCharge source) =
        ∑ _source ∈ input.sourceSet, (-1 : Int) := by
      apply Finset.sum_congr rfl
      intro source member
      have degree := (input.mem_sourceSet_iff source).1 member |>.2
      simp [Input.signedCharge, degree]
    _ = -(input.sourceSet.card : Int) := by simp

theorem receiver_charge_eq_capacity :
    (∑ receiver ∈ input.receiverSet, input.signedCharge receiver) =
      ∑ receiver ∈ input.receiverSet,
        ((input.receiverCapacity receiver : Nat) : Int) := by
  apply Finset.sum_congr rfl
  intro receiver member
  have degree := (input.mem_receiverSet_iff receiver).1 member |>.2
  have positive :
      1 ≤ input.parameters.scale *
        (input.parameters.sourceDegree - input.degree receiver) := by
    have diff_pos :
        0 < input.parameters.sourceDegree - input.degree receiver := by
      omega
    have product_pos :
        0 < input.parameters.scale *
          (input.parameters.sourceDegree - input.degree receiver) :=
      Nat.mul_pos input.parameters.scale_pos diff_pos
    omega
  unfold Input.signedCharge Input.receiverCapacity Parameters.capacity
  rw [Nat.cast_sub positive]
  norm_num

/-- Exact graph-level unsaturated receiver discharge. -/
theorem signedCharge_nonnegative (unsaturated : routing.Unsaturated) :
    0 ≤ ∑ vertex ∈ input.support, input.signedCharge vertex := by
  letI : DecidableEq Vertex := input.vertices.decEq
  have fibreBound :
      ∑ receiver ∈ input.receiverSet, routing.load receiver ≤
        ∑ receiver ∈ input.receiverSet, input.receiverCapacity receiver := by
    exact Finset.sum_le_sum fun receiver member =>
      unsaturated receiver member
  rw [← routing.source_card_eq_sum_load] at fibreBound
  have fibreBoundInt :
      (input.sourceSet.card : Int) ≤
        ∑ receiver ∈ input.receiverSet,
          ((input.receiverCapacity receiver : Nat) : Int) := by
    exact_mod_cast fibreBound
  rw [input.support_eq_partitionSet]
  unfold Input.partitionSet
  rw [Finset.sum_union input.source_disjoint_receivers]
  rw [source_charge_eq_neg_card (input := input),
    receiver_charge_eq_capacity (input := input)]
  omega

/-- Unconditional quantitative form of the receiver discharge.  Any negative
signed charge is bounded by the literal total overload of the chosen receiver
fibres.  The usual unsaturated theorem is the zero-overload special case. -/
theorem neg_signedCharge_le_totalOverload :
    -(∑ vertex ∈ input.support, input.signedCharge vertex) ≤
      (routing.totalOverload : Int) := by
  letI : DecidableEq Vertex := input.vertices.decEq
  have natural := routing.source_card_le_total_capacity_add_overload
  have castBound :
      (input.sourceSet.card : Int) ≤
        (∑ receiver ∈ input.receiverSet,
          ((input.receiverCapacity receiver : Nat) : Int)) +
            (routing.totalOverload : Int) := by
    exact_mod_cast natural
  rw [input.support_eq_partitionSet]
  unfold Input.partitionSet
  rw [Finset.sum_union input.source_disjoint_receivers]
  rw [source_charge_eq_neg_card (input := input),
    receiver_charge_eq_capacity (input := input)]
  omega

end Routing

end StructuralExhaustion.Core.FiniteReceiverDischarge
