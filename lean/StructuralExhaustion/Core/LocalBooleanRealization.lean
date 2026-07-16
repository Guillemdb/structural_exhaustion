import StructuralExhaustion.Core.BooleanStateEntropy
import StructuralExhaustion.Core.EnumerationCombinators
import StructuralExhaustion.Core.FiniteSearch

namespace StructuralExhaustion.Core.LocalBooleanRealization

universe uCoordinate uState

/-!
# Exhaustive local Boolean realization

This file supplies the decision layer deliberately omitted from
`BooleanStateEntropy`.  A caller gives one finite local coordinate/state
system.  The runner either constructs the exact complete-realization profile
consumed by the entropy theorem, or returns the first Boolean assignment that
no local state realizes.  Thus complete realization is an output of a local
finite decision, never a standing hypothesis and never a consequence of
coordinate injectivity.
-/

/-- One bounded local response system. -/
structure System where
  Coordinate : Type uCoordinate
  State : Type uState
  coordinates : FinEnum Coordinate
  states : FinEnum State
  value : State → Coordinate → Bool

namespace System

variable (system : System)

abbrev Assignment := system.Coordinate → Bool

@[implicit_reducible]
def assignments : FinEnum system.Assignment := by
  letI : FinEnum system.Coordinate := system.coordinates
  letI : FinEnum Bool := Enumeration.bool
  exact inferInstance

/-- The state search for one requested assignment. -/
def stateSearch (assignment : system.Assignment) :
    FiniteSearch.Result (fun state ↦ system.value state = assignment) :=
  FiniteSearch.search system.states
    (fun state ↦ system.value state = assignment)
    (fun _state ↦ by
      letI : FinEnum system.Coordinate := system.coordinates
      infer_instance)

/-- A concrete assignment omitted by every state in the local system. -/
def MissingAssignment (assignment : system.Assignment) : Prop :=
  ∀ state, system.value state ≠ assignment

def missingAssignmentDecidable (assignment : system.Assignment) :
    Decidable (system.MissingAssignment assignment) :=
  match system.stateSearch assignment with
  | .found state realized => isFalse fun missing => missing state realized
  | .absent absentProof => isTrue absentProof

/-- Ordered exhaustive scan for the first missing Boolean assignment. -/
def firstMissing : FiniteSearch.FirstResult
    system.assignments.orderedValues system.MissingAssignment :=
  FiniteSearch.first system.assignments system.MissingAssignment
    system.missingAssignmentDecidable

/-- Positive certificate carried by the hot branch. -/
structure HotCertificate : Prop where
  realizes : ∀ assignment : system.Assignment,
    ∃ state, system.value state = assignment

/-- Typed positive information carried by the cold branch. -/
structure ColdResidual where
  assignment : system.Assignment
  noState : ∀ state, system.value state ≠ assignment

/-- The complete local dichotomy.  Notice that the hot constructor contains
the realization proof needed by `BooleanStateEntropy.Profile`; callers cannot
manufacture a hot outcome from injectivity or rank data alone. -/
inductive Outcome where
  | hot (certificate : system.HotCertificate)
  | cold (residual : system.ColdResidual)

/-- Execute the local assignment scan. -/
def classify : system.Outcome := by
  cases result : system.firstMissing with
  | found hit =>
      exact Outcome.cold ⟨hit.value, hit.holds⟩
  | absent none =>
      apply Outcome.hot
      constructor
      intro assignment
      cases stateResult : system.stateSearch assignment with
      | found state holds => exact ⟨state, holds⟩
      | absent absentState =>
          have missing : system.MissingAssignment assignment := absentState
          exact (none assignment
            (system.assignments.mem_orderedValues assignment) missing).elim

/-- Every run is either genuinely hot or carries a genuine missing vector. -/
theorem classify_total :
    match system.classify with
    | .hot _certificate =>
        ∀ assignment, ∃ state, system.value state = assignment
    | .cold residual =>
        ∀ state, system.value state ≠ residual.assignment := by
  cases result : system.classify with
  | hot certificate => exact certificate.realizes
  | cold residual => exact residual.noState

/-- Convert only a verified hot certificate to the existing entropy
contract. -/
def HotCertificate.entropyProfile
    (certificate : system.HotCertificate) : BooleanStateEntropy.Profile where
  Coordinate := system.Coordinate
  State := system.State
  coordinates := system.coordinates
  states := system.states
  value := system.value
  realizes := certificate.realizes

/-- Exact entropy consequence available on, and only on, the hot branch. -/
theorem HotCertificate.two_pow_coordinateCard_le_stateCard
    (certificate : system.HotCertificate) :
    2 ^ system.coordinates.card ≤ system.states.card :=
  certificate.entropyProfile.two_pow_coordinateCard_le_stateCard

/-- A cold residual excludes complete Boolean realization without weakening
the surrounding theorem or requesting an additional assumption. -/
theorem ColdResidual.not_complete
    (residual : system.ColdResidual) :
    ¬(∀ assignment : system.Assignment,
      ∃ state, system.value state = assignment) := by
  intro complete
  obtain ⟨state, realized⟩ := complete residual.assignment
  exact residual.noState state realized

/-- The scan is local: its candidate universe has exactly `2^k`
assignments for `k` explicitly supplied coordinates. -/
theorem assignments_card :
    system.assignments.card = 2 ^ system.coordinates.card := by
  letI : FinEnum system.Coordinate := system.coordinates
  letI : FinEnum Bool := Enumeration.bool
  letI : FinEnum system.Assignment := system.assignments
  rw [FinEnum.card_eq_fintypeCard, Fintype.card_fun,
    ← FinEnum.card_eq_fintypeCard, ← FinEnum.card_eq_fintypeCard]
  rfl

end System

end StructuralExhaustion.Core.LocalBooleanRealization
