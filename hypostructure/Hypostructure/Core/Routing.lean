import Hypostructure.Core.Execution
import Hypostructure.Core.Residual.Focus

/-!
# Framework-owned accumulated routing

Routes consume one literal complete predecessor, perform registered semantic
discovery, execute the target entry internally, and add one generated result.
No successor or branch result is accepted from application code.
-/

namespace Hypostructure.Core.Routing

open Hypostructure.Core.Residual

universe uSource uInput uOutcome uTrace uSeed uBlocked uResidual

/-- Stable identifiers for the fixed CT family. -/
inductive CTId where
  | ct1 | ct2 | ct3 | ct4 | ct5 | ct6 | ct7 | ct8 | ct9
  | ct10 | ct11 | ct12 | ct13 | ct14 | ct15 | ct16 | ct17
  deriving Repr, DecidableEq

namespace CTId

/-- Stable positive catalog number. -/
def number : CTId -> Nat
  | .ct1 => 1
  | .ct2 => 2
  | .ct3 => 3
  | .ct4 => 4
  | .ct5 => 5
  | .ct6 => 6
  | .ct7 => 7
  | .ct8 => 8
  | .ct9 => 9
  | .ct10 => 10
  | .ct11 => 11
  | .ct12 => 12
  | .ct13 => 13
  | .ct14 => 14
  | .ct15 => 15
  | .ct16 => 16
  | .ct17 => 17

/-- Stable catalog spelling. -/
def key (id : CTId) : String := s!"CT{id.number}"

end CTId

/-- Stable registry identity for one executable transition profile. -/
structure Edge where
  source : CTId
  target : CTId
  profile : String
  deriving Repr, DecidableEq

namespace Edge

def familyKey (edge : Edge) : String :=
  edge.source.key ++ "->" ++ edge.target.key

def key (edge : Edge) : String :=
  edge.familyKey ++ ":" ++ edge.profile

end Edge

/-- Exhaustive semantic discovery performed inside a registered route. -/
inductive Discovery (Seed : Type uSeed) (Blocked : Type uBlocked) where
  | enabled (seed : Seed)
  | disabled (residual : Blocked)

/-- Domain or CT profile data from which Core builds a transition.  The
profile supplies semantic discovery and a target-input constructor; it does
not supply a target result. -/
structure Profile (Source : Type uSource) where
  Target : Execution.Spec.{uSource, uInput, uOutcome, uTrace} Source
  executor : Execution.Capability Target
  Seed : Source -> Type uSeed
  Blocked : Source -> Type uBlocked
  discover : (source : Source) -> Discovery (Seed source) (Blocked source)
  targetInput : (source : Source) -> Seed source -> Target.Input source

namespace Profile

/-- Disabled discovery payload for focus-derived routes. -/
structure FocusBlocked {Source : Type uSource}
    (focus : Focus.Profile Source) (source : Source) : Type where
  inactive : Not (focus.Active source)

/-- Build a route profile from a focused branch.  Core owns the handoff:
semantic discovery is enabled exactly when the source lies in the supplied
focus, and disabled otherwise.  The caller supplies only the active-branch
seed constructor and target-input map; it never supplies a routed result. -/
def ofFocus {Source : Type uSource}
    (focus : Focus.Profile Source)
    (target : Execution.Spec.{uSource, uInput, uOutcome, uTrace} Source)
    (executor : Execution.Capability target)
    (Seed : Source -> Type uSeed)
    (seed : (source : Source) -> (active : focus.Active source) ->
      Seed source)
    (targetInput :
      (source : Source) -> Seed source -> target.Input source) :
    Profile.{uSource, uInput, uOutcome, uTrace, uSeed, 0} Source where
  Target := target
  executor := executor
  Seed := Seed
  Blocked := FocusBlocked focus
  discover := fun source =>
    match (focus.select source).value with
    | .isTrue active => .enabled (seed source active)
    | .isFalse inactive => .disabled ⟨inactive⟩
  targetInput := fun source packed =>
    targetInput source packed

@[simp] theorem ofFocus_discover_active {Source : Type uSource}
    (focus : Focus.Profile Source)
    (target : Execution.Spec.{uSource, uInput, uOutcome, uTrace} Source)
    (executor : Execution.Capability target)
    (Seed : Source -> Type uSeed)
    (seed : (source : Source) -> (active : focus.Active source) ->
      Seed source)
    (targetInput :
      (source : Source) -> Seed source -> target.Input source)
    (source : Source) (active : focus.Active source) :
    ((ofFocus focus target executor Seed seed targetInput).discover source) =
      .enabled (seed source active) := by
  cases selected : (focus.select source).value with
  | isTrue selectedActive =>
      have equal : selectedActive = active := Subsingleton.elim _ _
      cases equal
      simp [ofFocus, selected]
  | isFalse inactive => exact (inactive active).elim

@[simp] theorem ofFocus_discover_inactive {Source : Type uSource}
    (focus : Focus.Profile Source)
    (target : Execution.Spec.{uSource, uInput, uOutcome, uTrace} Source)
    (executor : Execution.Capability target)
    (Seed : Source -> Type uSeed)
    (seed : (source : Source) -> (active : focus.Active source) ->
      Seed source)
    (targetInput :
      (source : Source) -> Seed source -> target.Input source)
    (source : Source) (inactive : Not (focus.Active source)) :
    ((ofFocus focus target executor Seed seed targetInput).discover source) =
      .disabled ⟨inactive⟩ := by
  cases selected : (focus.select source).value with
  | isTrue active => exact (inactive active).elim
  | isFalse selectedInactive =>
      have equal : selectedInactive = inactive := Subsingleton.elim _ _
      cases equal
      simp [ofFocus, selected]

end Profile

/-- Registered framework transition.  Its constructor is private so a route
result can only be produced through `advance`. -/
structure Transition (edge : Edge) (Source : Type uSource) where
  private mk ::
  profile : Profile.{uSource, uInput, uOutcome, uTrace, uSeed, uBlocked} Source

namespace Transition

/-- Register reusable semantic profile data under one stable edge identity. -/
def register (edge : Edge)
    (profile : Profile.{uSource, uInput, uOutcome, uTrace, uSeed, uBlocked}
      Source) : Transition edge Source :=
  .mk profile

/-- Target execution specification owned by a registered transition. -/
abbrev Target {edge : Edge} {Source : Type uSource}
    (transition : Transition.{uSource, uInput, uOutcome, uTrace, uSeed, uBlocked}
      edge Source) :=
  transition.profile.Target

end Transition

/-- Proof-relevant transition provenance retained in the generated result. -/
structure Provenance (edge : Edge) where
  private mk ::
  recorded : Edge
  exact_edge : recorded = edge

namespace Provenance

private def record (edge : Edge) : Provenance edge :=
  .mk edge rfl

end Provenance

/-- Framework-generated route result.  Its dependent execution field is
present exactly on the enabled branch; the disabled branch retains the typed
residual emitted by semantic discovery. -/
structure Result {edge : Edge} {Source : Type uSource}
    (transition : Transition.{uSource, uInput, uOutcome, uTrace, uSeed, uBlocked}
      edge Source)
    (source : Source) where
  private mk ::
  provenance : Provenance edge
  discovery : Discovery (transition.profile.Seed source)
    (transition.profile.Blocked source)
  canonical : discovery = transition.profile.discover source
  execution : match discovery with
    | .enabled seed =>
        Execution.Result transition.profile.Target source
          (transition.profile.targetInput source seed)
    | .disabled _ => PUnit

/-- One route is one extension of the literal complete incoming stage. -/
abbrev Stage {edge : Edge} {Source : Type uSource}
    (transition : Transition.{uSource, uInput, uOutcome, uTrace, uSeed, uBlocked}
      edge Source) :=
  Residual.Ledger.Extension Source (Result transition)

/-- Execute semantic discovery and, on the enabled outcome, invoke the public
target executor internally. -/
def advance {edge : Edge} {Source : Type uSource}
    (transition : Transition.{uSource, uInput, uOutcome, uTrace, uSeed, uBlocked}
      edge Source)
    (source : Source) : Stage transition :=
  match equation : transition.profile.discover source with
  | .enabled seed =>
      let executed := Execution.run transition.profile.executor source
        (transition.profile.targetInput source seed)
      Residual.Ledger.extend source <| .mk
        (Provenance.record edge) (.enabled seed) equation.symm
        executed.added.result
  | .disabled blocked =>
      Residual.Ledger.extend source <| .mk
        (Provenance.record edge) (.disabled blocked) equation.symm PUnit.unit

@[simp] theorem advance_previous {edge : Edge} {Source : Type uSource}
    (transition : Transition.{uSource, uInput, uOutcome, uTrace, uSeed, uBlocked}
      edge Source)
    (source : Source) : (advance transition source).previous = source := by
  unfold advance
  split <;> rfl

/-- The stored discovery is exactly the registered semantic discovery. -/
theorem advance_canonical {edge : Edge} {Source : Type uSource}
    (transition : Transition.{uSource, uInput, uOutcome, uTrace, uSeed, uBlocked}
      edge Source)
    (source : Source) :
    (advance transition source).added.discovery =
      transition.profile.discover (advance transition source).previous :=
  (advance transition source).added.canonical

/-- The runtime provenance record is the edge carried by the result type. -/
theorem advance_provenance {edge : Edge} {Source : Type uSource}
    (transition : Transition.{uSource, uInput, uOutcome, uTrace, uSeed, uBlocked}
      edge Source)
    (source : Source) :
    (advance transition source).added.provenance.recorded = edge :=
  (advance transition source).added.provenance.exact_edge

/-- Routing over an accumulated stage preserves its stable residual. -/
@[simp] theorem advance_residual {edge : Edge} {Source : Type uSource}
    {ResidualType : Type uResidual}
    [Residual.HasResidual Source ResidualType]
    (transition : Transition.{uSource, uInput, uOutcome, uTrace, uSeed, uBlocked}
      edge Source)
    (source : Source) :
    Residual.residualOf (advance transition source) =
      Residual.residualOf source := by
  unfold advance
  split <;> rfl

/-- Proof object used by acyclic route schedules and obstruction reduction. -/
structure StrictRankDecrease (sourceRank targetRank : Nat) : Prop where
  decreases : targetRank < sourceRank

namespace StrictRankDecrease

/-- Strict rank descent composes. -/
theorem trans {first middle last : Nat}
    (left : StrictRankDecrease first middle)
    (right : StrictRankDecrease middle last) :
    StrictRankDecrease first last :=
  ⟨Nat.lt_trans right.decreases left.decreases⟩

/-- Strict rank descent excludes a self-route at the same rank. -/
theorem not_same {rank : Nat} : Not (StrictRankDecrease rank rank) := by
  intro decrease
  exact (Nat.lt_irrefl rank) decrease.decreases

end StrictRankDecrease

end Hypostructure.Core.Routing
