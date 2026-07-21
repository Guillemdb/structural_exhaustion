import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

namespace StructuralExhaustion.Core.FixedTwoBoundaryCutState

universe uCoordinate uPrefix uContext

/-!
# Fixed two-boundary cut states

This is the normalized finite state used before a corridor first-failure
argument.  It stores roles, capped local data, and response bits only.  In
particular it stores neither ambient vertices nor a raw connector length.

The coordinates needed by D4--D7 are deliberately a parameter
`LocalCoordinate`.  Supplying a fixed finite alphabet and a graph-derived
projection onto it is the one remaining semantic obligation; the state
constructor itself does not invent such coordinates or claim completeness
for contexts outside the declared response family.
-/

abbrev BoundaryRole := Fin 2
abbrev CappedDegree := Fin 4
abbrev WindowOffset (windowLength : Nat) := Fin windowLength
abbrev TargetOffset (targetOffsetCount : Nat) := Fin targetOffsetCount

/-- Saturate a boundary degree at three. -/
def capDegree (degree : Nat) : CappedDegree :=
  ⟨min degree 3, by omega⟩

@[simp] theorem capDegree_val (degree : Nat) :
    (capDegree degree).val = min degree 3 := rfl

theorem capDegree_eq_of_lt_four {degree : Nat} (bounded : degree < 4) :
    (capDegree degree).val = degree := by
  simp [capDegree]
  omega

/-- Observe a connector length only through the declared finite target-offset
alphabet.  The framework does not choose the alphabet size; applications
instantiate it at their boundary. -/
def targetOffsetResponse (LengthOK : Nat → Prop)
    (lengthOKDecidable : DecidablePred LengthOK) (connectorLength : Nat) :
    TargetOffset targetOffsetCount → Bool :=
  fun offset ↦ decide (LengthOK (connectorLength + offset.val))

theorem targetOffsetResponse_eq_true_iff
    (LengthOK : Nat → Prop) (lengthOKDecidable : DecidablePred LengthOK)
    (connectorLength : Nat) (offset : TargetOffset targetOffsetCount) :
    targetOffsetResponse LengthOK lengthOKDecidable connectorLength offset = true ↔
      LengthOK (connectorLength + offset.val) := by
  simp [targetOffsetResponse]

/-- The ambient-independent normalized code. -/
structure State (windowLength targetOffsetCount : Nat)
    (LocalCoordinate : Type uCoordinate) where
  boundaryDegree : BoundaryRole → CappedDegree
  windowOffset : BoundaryRole → WindowOffset windowLength
  targetResponse : TargetOffset targetOffsetCount → Bool
  localResponse : LocalCoordinate → Bool

def stateEquiv (windowLength targetOffsetCount : Nat)
    (LocalCoordinate : Type uCoordinate) :
    State windowLength targetOffsetCount LocalCoordinate ≃
      ((BoundaryRole → CappedDegree) ×
        (BoundaryRole → WindowOffset windowLength) ×
        (TargetOffset targetOffsetCount → Bool) ×
        (LocalCoordinate → Bool)) where
  toFun state := (state.boundaryDegree, state.windowOffset,
    state.targetResponse, state.localResponse)
  invFun data := ⟨data.1, data.2.1, data.2.2.1, data.2.2.2⟩
  left_inv := by intro state; cases state; rfl
  right_inv := by intro data; rcases data with ⟨a, b, c, d⟩; rfl

instance (windowLength targetOffsetCount : Nat)
    (LocalCoordinate : Type uCoordinate) [Fintype LocalCoordinate]
    [DecidableEq LocalCoordinate] :
    DecidableEq (State windowLength targetOffsetCount LocalCoordinate) :=
  (stateEquiv windowLength targetOffsetCount LocalCoordinate).decidableEq

noncomputable instance (windowLength targetOffsetCount : Nat)
    (LocalCoordinate : Type uCoordinate) [Fintype LocalCoordinate] :
    Fintype (State windowLength targetOffsetCount LocalCoordinate) := by
  classical
  exact Fintype.ofEquiv _
    (stateEquiv windowLength targetOffsetCount LocalCoordinate).symm

/-- Exact cardinality of the normalized state.  It depends only on the fixed
local alphabet, never on an ambient vertex type or graph order. -/
theorem state_card (windowLength targetOffsetCount : Nat)
    (LocalCoordinate : Type uCoordinate)
    [Fintype LocalCoordinate] :
    Fintype.card (State windowLength targetOffsetCount LocalCoordinate) =
      4 ^ 2 * windowLength ^ 2 * 2 ^ targetOffsetCount *
        2 ^ Fintype.card LocalCoordinate := by
  classical
  rw [Fintype.card_congr
    (stateEquiv windowLength targetOffsetCount LocalCoordinate)]
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_bool]
  ring

/-- Phantom ambient-indexed presentation, useful when comparing producers on
different host vertex types.  The ambient type is intentionally absent from
the stored code. -/
abbrev StateFor (windowLength targetOffsetCount : Nat)
    (_Ambient : Type*) (LocalCoordinate : Type uCoordinate) :=
  State windowLength targetOffsetCount LocalCoordinate

theorem state_card_independent_of_ambient
    (windowLength targetOffsetCount : Nat)
    (LeftAmbient RightAmbient : Type*)
    (LocalCoordinate : Type uCoordinate) [Fintype LocalCoordinate] :
    Fintype.card
        (StateFor windowLength targetOffsetCount LeftAmbient LocalCoordinate) =
      Fintype.card
        (StateFor windowLength targetOffsetCount RightAmbient LocalCoordinate) := rfl

/-- The sole D4--D7 semantic input: a fixed finite coordinate alphabet and a
graph-derived bit on every prefix. -/
structure LocalProjection (Prefix : Type uPrefix)
    (LocalCoordinate : Type uCoordinate) where
  response : Prefix → LocalCoordinate → Bool

/-- Structural observations available on any corridor prefix.  Actual
interface identities may exist in the producer, but the projection below
forgets them and retains only their two fixed roles. -/
structure PrefixObservations (windowLength : Nat) (Prefix : Type uPrefix) where
  boundaryDegree : Prefix → BoundaryRole → Nat
  windowOffset : Prefix → BoundaryRole → WindowOffset windowLength
  connectorLength : Prefix → Nat

/-- Project any corridor prefix to the fixed normalized state. -/
def project (LengthOK : Nat → Prop)
    (lengthOKDecidable : DecidablePred LengthOK)
    {Prefix : Type uPrefix} {LocalCoordinate : Type uCoordinate}
    {windowLength targetOffsetCount : Nat}
    (observations : PrefixObservations windowLength Prefix)
    (localProjection : LocalProjection Prefix LocalCoordinate)
    (segment : Prefix) :
    State windowLength targetOffsetCount LocalCoordinate where
  boundaryDegree role := capDegree (observations.boundaryDegree segment role)
  windowOffset := observations.windowOffset segment
  targetResponse := targetOffsetResponse LengthOK lengthOKDecidable
    (observations.connectorLength segment)
  localResponse := localProjection.response segment

@[simp] theorem project_localResponse
    (LengthOK : Nat → Prop) (lengthOKDecidable : DecidablePred LengthOK)
    {Prefix : Type uPrefix} {LocalCoordinate : Type uCoordinate}
    {windowLength targetOffsetCount : Nat}
    (observations : PrefixObservations windowLength Prefix)
    (localProjection : LocalProjection Prefix LocalCoordinate) (segment : Prefix)
    (coordinate : LocalCoordinate) :
    (project (targetOffsetCount := targetOffsetCount) LengthOK
        lengthOKDecidable observations localProjection segment).localResponse
      coordinate = localProjection.response segment coordinate := rfl

@[simp] theorem project_boundaryDegree
    (LengthOK : Nat → Prop) (lengthOKDecidable : DecidablePred LengthOK)
    {Prefix : Type uPrefix} {LocalCoordinate : Type uCoordinate}
    {windowLength targetOffsetCount : Nat}
    (observations : PrefixObservations windowLength Prefix)
    (localProjection : LocalProjection Prefix LocalCoordinate) (segment : Prefix)
    (role : BoundaryRole) :
    (project (targetOffsetCount := targetOffsetCount) LengthOK
        lengthOKDecidable observations localProjection segment).boundaryDegree
      role = capDegree (observations.boundaryDegree segment role) := rfl

@[simp] theorem project_targetResponse
    (LengthOK : Nat → Prop) (lengthOKDecidable : DecidablePred LengthOK)
    {Prefix : Type uPrefix} {LocalCoordinate : Type uCoordinate}
    {windowLength targetOffsetCount : Nat}
    (observations : PrefixObservations windowLength Prefix)
    (localProjection : LocalProjection Prefix LocalCoordinate) (segment : Prefix)
    (offset : TargetOffset targetOffsetCount) :
    (project (targetOffsetCount := targetOffsetCount) LengthOK
        lengthOKDecidable observations localProjection segment).targetResponse
      offset = decide (LengthOK
        (observations.connectorLength segment + offset.val)) := rfl

/-- Typed F2 residual.  `Context` is only the explicitly declared context
family supplied by the consumer; it is not silently identified with all
outside graphs. -/
structure TargetResponseDistinction (Prefix : Type uPrefix)
    (Context : Type uContext) (response : Prefix → Context → Bool)
    (left right : Prefix) where
  context : Context
  differs : response left context ≠ response right context

/-- Exact both-sides result for two equal normalized codes. -/
inductive EqualCodeComparison
    {Prefix : Type uPrefix} {LocalCoordinate : Type uCoordinate}
    (localProjection : LocalProjection Prefix LocalCoordinate)
    (Context : Type uContext) (response : Prefix → Context → Bool)
    (left right : Prefix) : Type (max uCoordinate uContext) where
  | targetDistinction
      (residual : TargetResponseDistinction Prefix Context response left right)
  | declaredCoordinatesEqual
      (noDeclaredTargetDistinction :
        ¬Nonempty (TargetResponseDistinction Prefix Context response left right))
      (specificContextEquivalent : ∀ context,
        response left context = response right context)
      (equal : ∀ coordinate, localProjection.response left coordinate =
        localProjection.response right coordinate)

/-- Proof-carrying response equivalence for one specific pair. -/
structure SpecificContextEquivalence
    (Prefix : Type uPrefix) (Context : Type uContext)
    (response : Prefix → Context → Bool) (left right : Prefix) :
    Type (max uPrefix uContext) where
  equal : ∀ context, response left context = response right context

/-- Proof-producing F2 dichotomy for one specific pair.  This is an explicit
semantic obligation: it must come from structural path-set transport or a
local verified classifier, never from enumerating arbitrary outside graphs. -/
abbrev PairContextComparison
    (Prefix : Type uPrefix) (Context : Type uContext)
    (response : Prefix → Context → Bool) (left right : Prefix) :=
  TargetResponseDistinction Prefix Context response left right ⊕
    SpecificContextEquivalence Prefix Context response left right

/-- Both-sides comparison.  A supplied witnessed mismatch is retained as F2;
otherwise the supplied structural proof gives exact response equivalence for
this pair, while equal fixed codes give equality on declared local
coordinates.  No context search is performed here. -/
def compareEqualCodes
    (LengthOK : Nat → Prop) (lengthOKDecidable : DecidablePred LengthOK)
    {Prefix : Type uPrefix} {LocalCoordinate : Type uCoordinate}
    {windowLength targetOffsetCount : Nat}
    (observations : PrefixObservations windowLength Prefix)
    (localProjection : LocalProjection Prefix LocalCoordinate)
    (Context : Type uContext) (response : Prefix → Context → Bool)
    (left right : Prefix)
    (contextComparison :
      PairContextComparison Prefix Context response left right)
    (equalCode :
      project (targetOffsetCount := targetOffsetCount) LengthOK
          lengthOKDecidable observations localProjection left =
        project (targetOffsetCount := targetOffsetCount) LengthOK
          lengthOKDecidable observations localProjection right) :
    EqualCodeComparison localProjection Context response left right := by
  cases contextComparison with
  | inl distinguished =>
      exact EqualCodeComparison.targetDistinction distinguished
  | inr contextEquivalent =>
    refine EqualCodeComparison.declaredCoordinatesEqual ?_
      contextEquivalent.equal ?_
    · intro distinguished
      exact distinguished.some.differs
        (contextEquivalent.equal distinguished.some.context)
    intro coordinate
    have localFunctions := congrArg State.localResponse equalCode
    exact congrFun localFunctions coordinate

end StructuralExhaustion.Core.FixedTwoBoundaryCutState
