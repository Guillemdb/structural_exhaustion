import StructuralExhaustion.Core.FiniteSequentialFiltration
import StructuralExhaustion.Core.UniformFiniteFibreProduct

namespace StructuralExhaustion.Core.VariableConditionalFibreProductCost

universe uState uCoordinate

open StructuralExhaustion.Core.FiniteSequentialFiltration

/-!
# Variable-factor conditional-fibre product costs

This module runs an ordered list of local Boolean tests on one supplied finite
state schedule.  Each coordinate owns its own safe and flat factors.  A paying
run therefore proves a product inequality with those variable factors, while
the executable work ledger counts only tests on the current conditional fibre.
No product state space or ambient universe is enumerated.
-/

/-- One supplied finite state schedule, one ordered coordinate schedule, and
the exact local test and cost factors attached to each coordinate. -/
structure Profile where
  State : Type uState
  Coordinate : Type uCoordinate
  states : OrderedCollection State
  coordinates : OrderedCollection Coordinate
  accepts : Coordinate → State → Bool
  safe : Coordinate → Nat
  flat : Coordinate → Nat

namespace Profile

/-- The sequential-filtration barrier belonging to one coordinate. -/
def barrier (profile : Profile) (coordinate : profile.Coordinate) :
    Barrier profile.State where
  accepts := profile.accepts coordinate
  safe := profile.safe coordinate
  flat := profile.flat coordinate

/-- Barriers in the exact supplied coordinate order. -/
def barriers (profile : Profile) : List (Barrier profile.State) :=
  profile.coordinates.values.map profile.barrier

/-- The exact local fibre retained after testing one coordinate. -/
def retainAt (profile : Profile) (states : List profile.State)
    (coordinate : profile.Coordinate) : List profile.State :=
  states.filter (profile.accepts coordinate)

@[simp]
theorem retain_barrier_eq_retainAt (profile : Profile)
    (states : List profile.State) (coordinate : profile.Coordinate) :
    retain states (profile.barrier coordinate) =
      profile.retainAt states coordinate :=
  rfl

/-- Execute the ordered conditional-fibre filtration. -/
def run (profile : Profile) :
    Outcome profile.states.values profile.barriers :=
  runFrom profile.states.values profile.barriers

/-- Product of the coordinatewise safe factors. -/
def safeProduct (profile : Profile) : Nat :=
  (profile.coordinates.values.map profile.safe).prod

/-- Product of the coordinatewise flat factors. -/
def flatProduct (profile : Profile) : Nat :=
  (profile.coordinates.values.map profile.flat).prod

@[simp]
theorem barriers_safe_product (profile : Profile) :
    (profile.barriers.map Barrier.safe).prod = profile.safeProduct := by
  simp [barriers, barrier, safeProduct, Function.comp_def]

@[simp]
theorem barriers_flat_product (profile : Profile) :
    (profile.barriers.map Barrier.flat).prod = profile.flatProduct := by
  simp [barriers, barrier, flatProduct, Function.comp_def]

/-- A complete paying run telescopes the variable coordinate factors over the
literal nested fibres. -/
theorem complete_product_le (profile : Profile)
    (ledger : CompleteLedger profile.states.values profile.barriers) :
    profile.safeProduct * ledger.finalStates.length ≤
      profile.flatProduct * profile.states.values.length := by
  simpa using ledger.product_le

/-- Exact predicate-evaluation count for a coordinate suffix.  At each step
only the current conditional fibre is scanned. -/
def checksFrom (profile : Profile) (states : List profile.State) :
    List profile.Coordinate → Nat
  | [] => 0
  | coordinate :: coordinates =>
      states.length +
        checksFrom profile (profile.retainAt states coordinate) coordinates

/-- Exact work count of the reference local filtering schedule. -/
def checks (profile : Profile) : Nat :=
  profile.checksFrom profile.states.values profile.coordinates.values

@[simp]
theorem checksFrom_nil (profile : Profile) (states : List profile.State) :
    profile.checksFrom states [] = 0 :=
  rfl

@[simp]
theorem checksFrom_cons (profile : Profile) (states : List profile.State)
    (coordinate : profile.Coordinate) (coordinates : List profile.Coordinate) :
    profile.checksFrom states (coordinate :: coordinates) =
      states.length +
        profile.checksFrom (profile.retainAt states coordinate) coordinates :=
  rfl

theorem retainAt_length_le (profile : Profile) (states : List profile.State)
    (coordinate : profile.Coordinate) :
    (profile.retainAt states coordinate).length ≤ states.length := by
  exact List.length_filter_le _ _

/-- The local evaluator is linear in state count times coordinate count.  This
is a bound on the actual shrinking-fibre scan, not on a Cartesian state cube. -/
theorem checksFrom_le_mul (profile : Profile) (states : List profile.State)
    (coordinates : List profile.Coordinate) :
    profile.checksFrom states coordinates ≤
      states.length * coordinates.length := by
  induction coordinates generalizing states with
  | nil => simp
  | cons coordinate coordinates ih =>
      rw [checksFrom_cons, List.length_cons]
      have tailBound := ih (profile.retainAt states coordinate)
      have fibreBound := profile.retainAt_length_le states coordinate
      have scaled := Nat.mul_le_mul_right coordinates.length fibreBound
      calc
        states.length +
            profile.checksFrom (profile.retainAt states coordinate) coordinates ≤
            states.length +
              (profile.retainAt states coordinate).length * coordinates.length :=
          Nat.add_le_add_left tailBound states.length
        _ ≤ states.length + states.length * coordinates.length :=
          Nat.add_le_add_left scaled states.length
        _ = states.length * (coordinates.length + 1) := by
          rw [Nat.mul_add, Nat.mul_one, Nat.add_comm]

theorem checks_le_state_mul_coordinate (profile : Profile) :
    profile.checks ≤
      profile.states.values.length * profile.coordinates.values.length := by
  exact profile.checksFrom_le_mul _ _

end Profile

end StructuralExhaustion.Core.VariableConditionalFibreProductCost
