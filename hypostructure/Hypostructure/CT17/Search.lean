import Hypostructure.CT17.State
import Hypostructure.Core.Finite.Accounting
import Hypostructure.Core.Residual.Decision

/-!
# CT17 bounded searches and Core routing

All scans run over schedules queried from the same literal predecessor.  Core
selects compatibility, scale, survivor, and orbit branches; CT17 only supplies
their local predicates and complementary theorems.
-/

namespace Hypostructure.CT17

universe uPrevious uTarget uOffset uPosition uValue

variable {Previous : Type uPrevious}
  {spec : Spec.{uPrevious, uTarget, uOffset, uPosition, uValue} Previous}

/-- Primitive decision for incompatibility at one scheduled pair. -/
def incompatibleDecidable (capability : Capability spec)
    (previous : Previous)
    (pair : spec.Target previous × spec.Offset previous) :
    Decidable (Incompatible (spec := spec) previous pair) :=
  match capability.compatibleDecidable previous pair.1 pair.2 with
  | .isTrue compatible => .isFalse fun incompatible => incompatible compatible
  | .isFalse incompatible => .isTrue incompatible

/-- Canonical target-major, offset-minor compatibility scan. -/
def admissibilityScan (capability : Capability spec) (previous : Previous) :
    Core.Finite.Search.Execution (capability.pairScheduleAt previous)
      (Incompatible (spec := spec) previous) :=
  Core.Finite.Search.run (capability.pairScheduleAt previous)
    (Incompatible (spec := spec) previous)
    (incompatibleDecidable capability previous)

/-- Exact compatibility decisions executed before the first failure, or over
the complete pair schedule on success. -/
def admissibilityChecks (capability : Capability spec)
    (previous : Previous) : Nat :=
  Core.Finite.Accounting.executionChecks
    (admissibilityScan capability previous)

/-- Route the compatibility scan through Core's canonical first-hit split. -/
def routeAdmissibility (capability : Capability spec) (previous : Previous) :=
  Core.Finite.Search.route (admissibilityScan capability previous)

/-- Core decision for finite scale versus the strict orbit complement. -/
def scaleDecisionNode (capability : Capability spec) (previous : Previous) :
    Core.Residual.Decision.Node (CompatibleState capability previous)
      (fun _state => FiniteScaleState capability previous)
      (fun _state => OrbitScaleState capability previous) :=
  Core.Residual.Decision.Node.create
    (fun _state =>
      match Nat.decLe (capability.scaleAt previous)
          (capability.scaleLimitAt previous) with
      | .isTrue finite => .isTrue (FiniteScaleState.ofBound finite)
      | .isFalse notFinite => .isFalse fun finite => notFinite finite.finite)
    (by
      intro _state notFinite
      apply OrbitScaleState.ofLarge
      by_contra notLarge
      exact notFinite (FiniteScaleState.ofBound (Nat.le_of_not_gt notLarge)))

/-- Route the selected predecessor-owned scale without a caller-selected
branch constructor. -/
def routeScale (capability : Capability spec) (previous : Previous)
    (compatible : CompatibleState capability previous) :=
  (scaleDecisionNode capability previous).run compatible

/-- Primitive target-value equality at one finite block pair. -/
def blockHitDecidable (capability : Capability spec) (previous : Previous)
    (position : spec.Position previous (capability.scaleAt previous))
    (pair : spec.Target previous × spec.Offset previous) :
    Decidable (BlockHits capability previous position pair) := by
  unfold BlockHits
  exact capability.valueDecidableEq previous _ _

/-- Canonical target-major, offset-minor target search for one position. -/
def blockScan (capability : Capability spec) (previous : Previous)
    (position : spec.Position previous (capability.scaleAt previous)) :
    Core.Finite.Search.Execution (capability.pairScheduleAt previous)
      (BlockHits capability previous position) :=
  Core.Finite.Search.run (capability.pairScheduleAt previous)
    (BlockHits capability previous position)
    (blockHitDecidable capability previous position)

/-- Core-derived decidability of exact finite-block survival. -/
def survivesDecidable (capability : Capability spec) (previous : Previous)
    (position : spec.Position previous (capability.scaleAt previous)) :
    Decidable (Survives capability previous position) :=
  let routed := Core.Finite.Search.route
    (blockScan capability previous position)
  match routed.added with
  | .yesBranch hasHit =>
      .isFalse fun avoids =>
        let hit := routed.previous.hitOfHasHit hasHit
        avoids hit.index hit.holds
  | .noBranch avoids => .isTrue avoids

/-- Canonical ordered survivor list obtained by filtering only the inherited
position schedule. -/
def survivorList (capability : Capability spec) (previous : Previous) :
    List (spec.Position previous (capability.scaleAt previous)) :=
  letI : DecidablePred (Survives capability previous) :=
    survivesDecidable capability previous
  (capability.positionsAt previous).values.filter
    (Survives capability previous)

/-- Exact nested equality checks used to classify all inherited positions. -/
def survivorChecks (capability : Capability spec) (previous : Previous) : Nat :=
  ((capability.positionsAt previous).values.map fun position =>
    Core.Finite.Accounting.executionChecks
      (blockScan capability previous position)).sum

/-- Nested survivor work is bounded by the product of position and pair
schedule cardinalities. -/
theorem survivorChecks_le_product (capability : Capability spec)
    (previous : Previous) :
    survivorChecks capability previous <=
      (capability.positionsAt previous).card *
        (capability.pairScheduleAt previous).card := by
  unfold survivorChecks
  calc
    ((capability.positionsAt previous).values.map fun position =>
        Core.Finite.Accounting.executionChecks
          (blockScan capability previous position)).sum <=
        ((capability.positionsAt previous).values.map fun _position =>
          (capability.pairScheduleAt previous).card).sum := by
      apply List.sum_le_sum
      intro position _member
      exact Core.Finite.Accounting.executionChecks_le_card
        (blockScan capability previous position)
    _ = (capability.positionsAt previous).card *
        (capability.pairScheduleAt previous).card := by
      simp [Core.Finite.Enumeration.card]

/-- Exact framework-generated survivor enumeration. -/
structure SurvivorEnumeration (capability : Capability spec)
    (previous : Previous) where
  private mk ::
  survivors : List (spec.Position previous (capability.scaleAt previous))
  exact : survivors = survivorList capability previous
  nodup : survivors.Nodup
  sound : forall position, position ∈ survivors ->
    Survives capability previous position
  complete : forall position,
    position ∈ (capability.positionsAt previous).values ->
      Survives capability previous position -> position ∈ survivors
  checks : Nat
  checks_exact : checks = survivorChecks capability previous

/-- Build the unique survivor enumeration from the exact inherited schedule. -/
def enumerateSurvivors (capability : Capability spec) (previous : Previous) :
    SurvivorEnumeration capability previous where
  survivors := survivorList capability previous
  exact := rfl
  nodup := by
    unfold survivorList
    exact (capability.positionsAt previous).nodup.filter _
  sound := by
    intro position member
    unfold survivorList at member
    simp only [List.mem_filter] at member
    simpa using member.2
  complete := by
    intro position scheduled survives
    unfold survivorList
    simp only [List.mem_filter]
    exact ⟨scheduled, by simp [survives]⟩
  checks := survivorChecks capability previous
  checks_exact := rfl

namespace SurvivorEnumeration

/-- Exact enumeration work satisfies the inherited product bound. -/
theorem checks_le_product {capability : Capability spec}
    {previous : Previous}
    (enumeration : SurvivorEnumeration capability previous) :
    enumeration.checks <= (capability.positionsAt previous).card *
      (capability.pairScheduleAt previous).card := by
  rw [enumeration.checks_exact]
  exact survivorChecks_le_product capability previous

end SurvivorEnumeration

/-- A finite-scale enumeration with no surviving scheduled position. -/
structure ExhaustedCertificate (capability : Capability spec)
    (previous : Previous) where
  private mk ::
  enumeration : SurvivorEnumeration capability previous
  exhausted : forall position,
    position ∈ (capability.positionsAt previous).values ->
      Not (Survives capability previous position)

/-- A nonempty finite-scale survivor enumeration, split canonically at its
head without defining another carrier. -/
structure SurvivorResidual (capability : Capability spec)
    (previous : Previous) where
  private mk ::
  enumeration : SurvivorEnumeration capability previous
  first : spec.Position previous (capability.scaleAt previous)
  remaining : List (spec.Position previous (capability.scaleAt previous))
  exact : enumeration.survivors = first :: remaining

namespace SurvivorResidual

/-- Package the head decomposition selected from Core's nonempty branch. -/
def ofNonempty {capability : Capability spec} {previous : Previous}
    (enumeration : SurvivorEnumeration capability previous)
    (nonempty : enumeration.survivors ≠ []) :
    SurvivorResidual capability previous := by
  cases exact : enumeration.survivors with
  | nil => exact (nonempty exact).elim
  | cons first remaining => exact .mk enumeration first remaining exact

/-- The canonical first survivor is in the exact position schedule. -/
theorem first_mem {capability : Capability spec} {previous : Previous}
    (residual : SurvivorResidual capability previous) :
    residual.first ∈ (capability.positionsAt previous).values := by
  have inSurvivors : residual.first ∈ residual.enumeration.survivors := by
    rw [residual.exact]
    simp
  rw [residual.enumeration.exact] at inSurvivors
  unfold survivorList at inSurvivors
  exact (List.mem_filter.mp inSurvivors).1

/-- The canonical first survivor has no block target hit. -/
theorem first_survives {capability : Capability spec} {previous : Previous}
    (residual : SurvivorResidual capability previous) :
    Survives capability previous residual.first := by
  apply residual.enumeration.sound
  rw [residual.exact]
  simp

end SurvivorResidual

/-- Core's positive proposition for the survivor-list split. -/
def HasSurvivor {capability : Capability spec} {previous : Previous}
    (enumeration : SurvivorEnumeration capability previous) : Prop :=
  enumeration.survivors ≠ []

/-- Core's generated complementary proposition for the survivor-list split. -/
def Exhausted {capability : Capability spec} {previous : Previous}
    (_enumeration : SurvivorEnumeration capability previous) : Prop :=
  forall position,
    position ∈ (capability.positionsAt previous).values ->
      Not (Survives capability previous position)

namespace ExhaustedCertificate

/-- Package the complementary proposition selected by Core. -/
def ofExhaustion {capability : Capability spec} {previous : Previous}
    (enumeration : SurvivorEnumeration capability previous)
    (exhausted : Exhausted enumeration) :
    ExhaustedCertificate capability previous :=
  .mk enumeration exhausted

end ExhaustedCertificate

/-- Core decision node for nonempty survivors versus exact exhaustion. -/
def survivorDecisionNode (capability : Capability spec) (previous : Previous) :
    Core.Residual.Decision.Node (SurvivorEnumeration capability previous)
      HasSurvivor Exhausted :=
  Core.Residual.Decision.Node.create
    (fun enumeration =>
      match exact : enumeration.survivors with
      | [] => .isFalse fun nonempty => nonempty exact
      | _first :: _remaining => .isTrue (by
          intro empty
          rw [exact] at empty
          simp at empty))
    (by
      intro enumeration noSurvivor position scheduled survives
      apply noSurvivor
      intro empty
      have member := enumeration.complete position scheduled survives
      rw [empty] at member
      exact List.not_mem_nil member)

/-- Route exact exhaustion versus a nonempty survivor residual through Core. -/
def routeSurvivors (capability : Capability spec) (previous : Previous)
    (enumeration : SurvivorEnumeration capability previous) :=
  (survivorDecisionNode capability previous).run enumeration

/-- Primitive orbit target-value equality. -/
def orbitHitDecidable (capability : Capability spec) (previous : Previous)
    (pair : spec.Target previous × spec.Offset previous) :
    Decidable (OrbitHits capability previous pair) := by
  unfold OrbitHits
  exact capability.valueDecidableEq previous _ _

/-- Canonical orbit target search. -/
def arithmeticScan (capability : Capability spec) (previous : Previous) :
    Core.Finite.Search.Execution (capability.pairScheduleAt previous)
      (OrbitHits capability previous) :=
  Core.Finite.Search.run (capability.pairScheduleAt previous)
    (OrbitHits capability previous) (orbitHitDecidable capability previous)

/-- Core-owned target-hit versus orbit-avoidance route. -/
def routeArithmetic (capability : Capability spec) (previous : Previous) :=
  Core.Finite.Search.route (arithmeticScan capability previous)

/-- Canonical first target hit in the selected orbit slice. -/
abbrev TargetHitCertificate (capability : Capability spec)
    (previous : Previous) :=
  Core.Finite.Search.IndexedHit (capability.pairScheduleAt previous)
    (OrbitHits capability previous)

namespace TargetHitCertificate

/-- Target selected by the orbit scan. -/
def target {capability : Capability spec} {previous : Previous}
    (certificate : TargetHitCertificate capability previous) :=
  certificate.value.1

/-- Offset selected by the orbit scan. -/
def offset {capability : Capability spec} {previous : Previous}
    (certificate : TargetHitCertificate capability previous) :=
  certificate.value.2

/-- The selected pair realizes the target value exactly. -/
theorem equal {capability : Capability spec} {previous : Previous}
    (certificate : TargetHitCertificate capability previous) :
    spec.orbitValue previous (capability.scaleAt previous)
        certificate.offset =
      spec.targetValue previous certificate.target :=
  certificate.sound

end TargetHitCertificate

/-- Target-avoiding orbit values computed on the exact inherited offset
schedule. -/
structure OrbitResidual (capability : Capability spec)
    (previous : Previous) where
  private mk ::
  values : List (spec.Value previous)
  values_exact : values = (capability.offsetsAt previous).values.map
    (spec.orbitValue previous (capability.scaleAt previous))
  avoids : OrbitAvoids capability previous

namespace OrbitResidual

/-- Build the canonical orbit residual from Core's exhaustive miss. -/
def ofAvoidance {capability : Capability spec} {previous : Previous}
    (avoids : OrbitAvoids capability previous) :
    OrbitResidual capability previous :=
  .mk ((capability.offsetsAt previous).values.map
    (spec.orbitValue previous (capability.scaleAt previous))) rfl avoids

end OrbitResidual

end Hypostructure.CT17
