import StructuralExhaustion.Core.BooleanStateEntropy

namespace StructuralExhaustion.Examples.BooleanStateEntropy

open StructuralExhaustion

/-! A two-coordinate, four-state transfer check for the generic entropy
contract.  This is a fixed textbook Boolean cube, not a graph enumeration. -/

def profile : Core.BooleanStateEntropy.Profile where
  Coordinate := Bool
  State := Bool × Bool
  coordinates := Core.Enumeration.bool
  states := FinEnum.ofNodupList
    [(false, false), (false, true), (true, false), (true, true)]
    (by
      rintro ⟨first, second⟩
      cases first <;> cases second <;> simp)
    (by decide)
  value := fun state coordinate ↦ if coordinate then state.2 else state.1
  realizes := by
    intro assignment
    refine ⟨(assignment false, assignment true), ?_⟩
    funext coordinate
    cases coordinate <;> simp

example : 2 ^ profile.coordinates.card ≤ profile.states.card :=
  profile.two_pow_coordinateCard_le_stateCard

/-! The next fixed three-state system records the exact logical distinction
used by the entropy contract.  Both labels remain distinct and each coordinate
takes both Boolean values, but the joint `true,true` state is absent. -/

inductive ThreeState where
  | zero
  | right
  | left
  deriving DecidableEq

def threeStateValue : ThreeState → Bool → Bool
  | .zero, _ => false
  | .right, false => false
  | .right, true => true
  | .left, false => true
  | .left, true => false

def coordinateCode (coordinate : Bool) : Nat :=
  if coordinate then 1 else 0

theorem coordinateCode_injective : Function.Injective coordinateCode := by
  intro left right equal
  cases left <;> cases right <;> simp [coordinateCode] at equal ⊢

theorem eachCoordinate_realizes_both (coordinate : Bool) :
    (∃ state, threeStateValue state coordinate = false) ∧
      ∃ state, threeStateValue state coordinate = true := by
  cases coordinate
  · exact ⟨⟨.zero, rfl⟩, ⟨.left, rfl⟩⟩
  · exact ⟨⟨.zero, rfl⟩, ⟨.right, rfl⟩⟩

/-- Every quotient code that preserves the response of identified
coordinates in every supplied context is label-injective.  Thus this finite
system satisfies the exact context-universal injectivity conclusion used by
an admissible-quotient rank ledger. -/
theorem everyContext_responsePreservingCode_injective
    (code : Bool → Nat)
    (responsePreserving : ∀ {left right}, code left = code right →
      ∀ state, threeStateValue state left = threeStateValue state right) :
    Function.Injective code := by
  intro left right identified
  cases left <;> cases right
  · rfl
  · have impossible := responsePreserving identified ThreeState.right
    simp [threeStateValue] at impossible
  · have impossible := responsePreserving identified ThreeState.right
    simp [threeStateValue] at impossible
  · rfl

/-- Label injectivity and separate two-value tests do not realize the complete
Boolean cube. -/
theorem true_true_not_realized :
    ¬∃ state, ∀ coordinate, threeStateValue state coordinate = true := by
  rintro ⟨state, realized⟩
  cases state
  · have impossible := realized false
    simp [threeStateValue] at impossible
  · have impossible := realized false
    simp [threeStateValue] at impossible
  · have impossible := realized true
    simp [threeStateValue] at impossible

/-- Context-universal label injectivity still does not provide realization of
the complete Boolean cube. -/
theorem responsePreservingInjectivity_does_not_realize_cube :
    (∀ (code : Bool → Nat),
      (∀ {left right}, code left = code right →
        ∀ state, threeStateValue state left = threeStateValue state right) →
      Function.Injective code) ∧
      ¬∃ state, ∀ coordinate, threeStateValue state coordinate = true :=
  ⟨everyContext_responsePreservingCode_injective, true_true_not_realized⟩

end StructuralExhaustion.Examples.BooleanStateEntropy
