import StructuralExhaustion.Core.Enumeration
import StructuralExhaustion.Core.WorkBudget

namespace StructuralExhaustion.Core.ConditionalFibreProductCost

open StructuralExhaustion

universe u v

/-!
# Conditional-fibre product costs

This profile checks an ordered list of local coordinates against one supplied
finite state list.  Each coordinate filters only the fibre retained by the
previous coordinates.  Thus the implementation never constructs assignments,
subsets, graphs, or a Boolean cube.

At every coordinate the local certificate proves

`safe * nextCount <= flat * currentCount`.

The inductive ledger telescopes these exact conditional counts.  A supplied
initial skeleton capacity and a nonempty final fibre then give

`safe ^ r <= flat ^ r * skeletonCount`,

where `r` is the length of the coordinate schedule.
-/

/-- Core data for one finite conditional-fibre calculation. -/
structure Profile where
  State : Type u
  Coordinate : Type v
  states : Core.OrderedCollection State
  coordinates : Core.OrderedCollection Coordinate
  accepts : Coordinate → State → Bool
  safe : Nat
  flat : Nat
  skeletonCount : Nat

namespace Profile

/-- The next exact conditional fibre. -/
def retain (profile : Profile.{u, v}) (states : List profile.State)
    (coordinate : profile.Coordinate) : List profile.State :=
  states.filter (profile.accepts coordinate)

/-- Apply a supplied coordinate prefix in schedule order. -/
def statesAfter (profile : Profile.{u, v}) :
    List profile.State → List profile.Coordinate → List profile.State
  | states, [] => states
  | states, coordinate :: coordinates =>
      statesAfter profile (profile.retain states coordinate) coordinates

/-- Exact survivor fibre after the first `prefixLength` coordinates. -/
def prefixStates (profile : Profile.{u, v}) (prefixLength : Nat) :
    List profile.State :=
  profile.statesAfter profile.states.values
    (profile.coordinates.values.take prefixLength)

/-- Exact per-prefix survivor count. -/
def prefixCount (profile : Profile.{u, v}) (prefixLength : Nat) : Nat :=
  (profile.prefixStates prefixLength).length

@[simp]
theorem statesAfter_nil (profile : Profile.{u, v})
    (states : List profile.State) :
    profile.statesAfter states [] = states := rfl

@[simp]
theorem statesAfter_cons (profile : Profile.{u, v})
    (states : List profile.State) (coordinate : profile.Coordinate)
    (coordinates : List profile.Coordinate) :
    profile.statesAfter states (coordinate :: coordinates) =
      profile.statesAfter (profile.retain states coordinate) coordinates := rfl

theorem statesAfter_append (profile : Profile.{u, v})
    (states : List profile.State) (first second : List profile.Coordinate) :
    profile.statesAfter states (first ++ second) =
      profile.statesAfter (profile.statesAfter states first) second := by
  induction first generalizing states with
  | nil => rfl
  | cons coordinate coordinates ih =>
      simp only [List.cons_append, statesAfter_cons]
      exact ih (profile.retain states coordinate)

theorem statesAfter_sublist (profile : Profile.{u, v})
    (states : List profile.State) (coordinates : List profile.Coordinate) :
    List.Sublist (profile.statesAfter states coordinates) states := by
  induction coordinates generalizing states with
  | nil => exact List.Sublist.refl _
  | cons coordinate coordinates ih =>
      exact (ih (profile.retain states coordinate)).trans List.filter_sublist

/-- Every prefix fibre is nested inside the original supplied state list. -/
theorem prefixStates_sublist_states (profile : Profile.{u, v})
    (prefixLength : Nat) :
    List.Sublist (profile.prefixStates prefixLength) profile.states.values :=
  profile.statesAfter_sublist _ _

/-- Later prefix fibres are nested in earlier prefix fibres.  This is the
formal prefix-predicate monotonicity used by conditional counting arguments. -/
theorem prefixStates_nested (profile : Profile.{u, v})
    {earlier later : Nat} (ordered : earlier ≤ later) :
    List.Sublist (profile.prefixStates later)
      (profile.prefixStates earlier) := by
  let schedule := profile.coordinates.values
  let remainder := (schedule.take later).drop earlier
  have decomposition : schedule.take later =
      schedule.take earlier ++ remainder := by
    rw [← List.take_append_drop earlier (schedule.take later)]
    congr 1
    simp [List.take_take, Nat.min_eq_left ordered]
  unfold prefixStates
  rw [decomposition, profile.statesAfter_append]
  exact profile.statesAfter_sublist _ _

/-- Membership in the exact retained fibre after a prefix. -/
def SurvivesPrefix (profile : Profile.{u, v})
    (prefixLength : Nat) (state : profile.State) : Prop :=
  state ∈ profile.prefixStates prefixLength

instance (profile : Profile.{u, v}) (prefixLength : Nat)
    (state : profile.State) :
    Decidable (profile.SurvivesPrefix prefixLength state) := by
  letI : DecidableEq profile.State := profile.states.decEq
  unfold SurvivesPrefix
  exact inferInstance

/-- A state surviving a later prefix survives every earlier prefix. -/
theorem survivesPrefix_mono (profile : Profile.{u, v})
    {earlier later : Nat} (ordered : earlier ≤ later)
    {state : profile.State}
    (survives : profile.SurvivesPrefix later state) :
    profile.SurvivesPrefix earlier state :=
  (profile.prefixStates_nested ordered).subset survives

/-- The exact initial fibre and count. -/
@[simp]
theorem prefixStates_zero (profile : Profile.{u, v}) :
    profile.prefixStates 0 = profile.states.values := by
  simp [prefixStates]

@[simp]
theorem prefixCount_zero (profile : Profile.{u, v}) :
    profile.prefixCount 0 = profile.states.values.length := by
  simp [prefixCount]

/-- Proof-carrying local inequalities for the literal coordinate schedule. -/
inductive Ledger (profile : Profile.{u, v}) :
    List profile.State → List profile.Coordinate → Type (max u v)
  | nil (states : List profile.State) : Ledger profile states []
  | cons {states : List profile.State} {coordinate : profile.Coordinate}
      {coordinates : List profile.Coordinate}
      (step : profile.safe * (profile.retain states coordinate).length ≤
        profile.flat * states.length)
      (tail : Ledger profile (profile.retain states coordinate) coordinates) :
      Ledger profile states (coordinate :: coordinates)

namespace Ledger

/-- Exact final fibre carried by a complete local schedule ledger. -/
def finalStates {profile : Profile.{u, v}} {states : List profile.State} :
    {coordinates : List profile.Coordinate} →
      Ledger profile states coordinates → List profile.State
  | [], .nil _ => states
  | _ :: _, .cons _ tail => tail.finalStates

/-- The ledger's terminal fibre is definitionally the iterated local filter. -/
theorem finalStates_eq_statesAfter {profile : Profile.{u, v}}
    {states : List profile.State} {coordinates : List profile.Coordinate}
    (ledger : Ledger profile states coordinates) :
    ledger.finalStates = profile.statesAfter states coordinates := by
  induction ledger with
  | nil states => rfl
  | @cons states coordinate coordinates step tail ih =>
      simpa [finalStates, Profile.statesAfter] using ih

/-- Every carried fibre remains a literal sublist of the starting fibre. -/
theorem finalStates_sublist {profile : Profile.{u, v}}
    {states : List profile.State} {coordinates : List profile.Coordinate}
    (ledger : Ledger profile states coordinates) :
    List.Sublist ledger.finalStates states := by
  rw [ledger.finalStates_eq_statesAfter]
  exact profile.statesAfter_sublist states coordinates

/-- Uniform local costs telescope over the complete coordinate schedule. -/
theorem power_product_le {profile : Profile.{u, v}}
    {states : List profile.State} {coordinates : List profile.Coordinate}
    (ledger : Ledger profile states coordinates) :
    profile.safe ^ coordinates.length * ledger.finalStates.length ≤
      profile.flat ^ coordinates.length * states.length := by
  induction ledger with
  | nil states => simp [finalStates]
  | @cons states coordinate coordinates step tail ih =>
      simp only [List.length_cons, pow_succ, finalStates]
      have first := Nat.mul_le_mul_left profile.safe ih
      have second := Nat.mul_le_mul_right (profile.flat ^ coordinates.length) step
      exact le_trans
        (by
          simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using first)
        (by
          simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using second)

end Ledger

/-- Complete certificate for the reusable finite product-cost conclusion. -/
structure Certificate (profile : Profile.{u, v}) where
  ledger : Ledger profile profile.states.values profile.coordinates.values
  startCapacity : profile.states.values.length ≤ profile.skeletonCount
  finalNonempty : 0 < ledger.finalStates.length

namespace Certificate

/-- The final certificate fibre is the exact full-schedule survivor list. -/
theorem finalStates_eq_prefixStates (profile : Profile.{u, v})
    (certificate : Certificate profile) :
    certificate.ledger.finalStates =
      profile.prefixStates profile.coordinates.values.length := by
  rw [certificate.ledger.finalStates_eq_statesAfter]
  simp [prefixStates]

/-- The exact full-prefix survivor count is positive. -/
theorem finalPrefixCount_pos (profile : Profile.{u, v})
    (certificate : Certificate profile) :
    0 < profile.prefixCount profile.coordinates.values.length := by
  unfold prefixCount
  rw [← certificate.finalStates_eq_prefixStates profile]
  exact certificate.finalNonempty

/-- Telescoping stated directly with the exact initial and final prefix
counts exposed by the public profile API. -/
theorem power_mul_finalPrefixCount_le (profile : Profile.{u, v})
    (certificate : Certificate profile) :
    profile.safe ^ profile.coordinates.values.length *
        profile.prefixCount profile.coordinates.values.length ≤
      profile.flat ^ profile.coordinates.values.length *
        profile.prefixCount 0 := by
  rw [profile.prefixCount_zero]
  unfold prefixCount
  rw [← certificate.finalStates_eq_prefixStates profile]
  exact certificate.ledger.power_product_le

/-- Main conditional-fibre product-cost theorem. -/
theorem power_le_flat_mul_skeleton (profile : Profile.{u, v})
    (certificate : Certificate profile) :
    profile.safe ^ profile.coordinates.values.length ≤
      profile.flat ^ profile.coordinates.values.length *
        profile.skeletonCount := by
  have nonemptyFactor : 1 ≤ certificate.ledger.finalStates.length :=
    certificate.finalNonempty
  have lower : profile.safe ^ profile.coordinates.values.length ≤
      profile.safe ^ profile.coordinates.values.length *
        certificate.ledger.finalStates.length := by
    simpa using Nat.mul_le_mul_left
      (profile.safe ^ profile.coordinates.values.length) nonemptyFactor
  have telescoped := certificate.ledger.power_product_le
  have capacity := Nat.mul_le_mul_left
    (profile.flat ^ profile.coordinates.values.length)
    certificate.startCapacity
  exact lower.trans (telescoped.trans capacity)

end Certificate

/-! The checker touches each state at most once for each supplied coordinate:
after a test, later scans inspect only the retained sublist. -/

/-- Exact number of primitive `accepts` calls in the one-pass checker. -/
def checksFrom (profile : Profile.{u, v}) :
    List profile.State → List profile.Coordinate → Nat
  | _states, [] => 0
  | states, coordinate :: coordinates =>
      states.length +
        checksFrom profile (profile.retain states coordinate) coordinates

/-- The checker performs at most `states * coordinates` local predicate calls. -/
theorem checksFrom_le_mul (profile : Profile.{u, v})
    (states : List profile.State) (coordinates : List profile.Coordinate) :
    profile.checksFrom states coordinates ≤ states.length * coordinates.length := by
  induction coordinates generalizing states with
  | nil => simp [checksFrom]
  | cons coordinate coordinates ih =>
      have retainedLength : (profile.retain states coordinate).length ≤ states.length :=
        List.length_filter_le _ _
      calc
        profile.checksFrom states (coordinate :: coordinates) =
            states.length + profile.checksFrom
              (profile.retain states coordinate) coordinates := rfl
        _ ≤ states.length +
            (profile.retain states coordinate).length * coordinates.length :=
          Nat.add_le_add_left (ih (profile.retain states coordinate)) _
        _ ≤ states.length + states.length * coordinates.length :=
          Nat.add_le_add_left
            (Nat.mul_le_mul_right coordinates.length retainedLength) _
        _ = states.length * (coordinate :: coordinates).length := by
          simp [Nat.mul_succ, Nat.add_comm]

def checks (profile : Profile.{u, v}) : Nat :=
  profile.checksFrom profile.states.values profile.coordinates.values

theorem checks_le_state_mul_coordinate (profile : Profile.{u, v}) :
    profile.checks ≤
      profile.states.values.length * profile.coordinates.values.length :=
  profile.checksFrom_le_mul _ _

/-- A quadratic bound in the combined explicit input size. -/
def budget (profile : Profile.{u, v}) : Core.PolynomialCheckBudget Unit where
  size := fun _ =>
    profile.states.values.length + profile.coordinates.values.length
  checks := fun _ => profile.checks
  coefficient := 1
  degree := 2
  bounded := by
    intro _
    calc
      profile.checks ≤
          profile.states.values.length * profile.coordinates.values.length :=
        profile.checks_le_state_mul_coordinate
      _ ≤ (profile.states.values.length +
          profile.coordinates.values.length + 1) ^ 2 := by
        rw [pow_two]
        apply Nat.mul_le_mul
        · omega
        · omega
      _ = 1 * (profile.states.values.length +
          profile.coordinates.values.length + 1) ^ 2 := by simp

end Profile

end StructuralExhaustion.Core.ConditionalFibreProductCost
