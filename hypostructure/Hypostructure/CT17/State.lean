import Hypostructure.CT17.Capability
import Hypostructure.Core.Finite.Search

/-!
# CT17 predecessor-indexed states

The compatibility, block, and orbit predicates are interpreted only on exact
schedules read from the predecessor.  None of these statements quantifies
over an ambient finite type or manufactures a replacement carrier.
-/

namespace Hypostructure.CT17

universe uPrevious uTarget uOffset uPosition uValue

variable {Previous : Type uPrevious}
  {spec : Spec.{uPrevious, uTarget, uOffset, uPosition, uValue} Previous}

/-- Failure predicate on the inherited target-offset schedule. -/
def Incompatible (previous : Previous)
    (pair : spec.Target previous × spec.Offset previous) : Prop :=
  Not (spec.Compatible previous pair.1 pair.2)

/-- A block comparison hits a declared target value. -/
def BlockHits (capability : Capability spec) (previous : Previous)
    (position : spec.Position previous (capability.scaleAt previous))
    (pair : spec.Target previous × spec.Offset previous) : Prop :=
  spec.blockValue previous (capability.scaleAt previous) position pair.2 =
    spec.targetValue previous pair.1

/-- An orbit comparison hits a declared target value. -/
def OrbitHits (capability : Capability spec) (previous : Previous)
    (pair : spec.Target previous × spec.Offset previous) : Prop :=
  spec.orbitValue previous (capability.scaleAt previous) pair.2 =
    spec.targetValue previous pair.1

/-- Canonical first incompatible pair in target-major, offset-minor order. -/
abbrev IncompatibilityResidual (capability : Capability spec)
    (previous : Previous) :=
  Core.Finite.Search.IndexedHit (capability.pairScheduleAt previous)
    (Incompatible (spec := spec) previous)

/-- Exhaustive compatibility on the exact inherited pair schedule. -/
abbrev CompatibleState (capability : Capability spec)
    (previous : Previous) :=
  Core.Finite.Search.Avoids (capability.pairScheduleAt previous)
    (Incompatible (spec := spec) previous)

namespace IncompatibilityResidual

/-- Incompatible target selected by the canonical scan. -/
def target {capability : Capability spec} {previous : Previous}
    (residual : IncompatibilityResidual capability previous) :
    spec.Target previous :=
  residual.value.1

/-- Incompatible offset selected by the canonical scan. -/
def offset {capability : Capability spec} {previous : Previous}
    (residual : IncompatibilityResidual capability previous) :
    spec.Offset previous :=
  residual.value.2

/-- The selected pair belongs to the exact inherited product schedule. -/
theorem pair_mem {capability : Capability spec} {previous : Previous}
    (residual : IncompatibilityResidual capability previous) :
    residual.value ∈ (capability.pairScheduleAt previous).values :=
  residual.member

/-- The selected target belongs to the inherited target schedule. -/
theorem target_mem {capability : Capability spec} {previous : Previous}
    (residual : IncompatibilityResidual capability previous) :
    residual.target ∈ (capability.targetsAt previous).values :=
  (Core.Finite.Enumeration.mem_product_values _ _ residual.value).mp
    residual.pair_mem |>.1

/-- The selected offset belongs to the inherited offset schedule. -/
theorem offset_mem {capability : Capability spec} {previous : Previous}
    (residual : IncompatibilityResidual capability previous) :
    residual.offset ∈ (capability.offsetsAt previous).values :=
  (Core.Finite.Enumeration.mem_product_values _ _ residual.value).mp
    residual.pair_mem |>.2

/-- The selected pair really is incompatible. -/
theorem incompatible {capability : Capability spec} {previous : Previous}
    (residual : IncompatibilityResidual capability previous) :
    Not (spec.Compatible previous residual.target residual.offset) :=
  residual.sound

end IncompatibilityResidual

namespace CompatibleState

/-- Exhaustive avoidance of incompatibility proves compatibility for every
pair in the exact predecessor-owned schedules. -/
theorem compatible {capability : Capability spec} {previous : Previous}
    (state : CompatibleState capability previous)
    (target : spec.Target previous)
    (targetMember : target ∈ (capability.targetsAt previous).values)
    (offset : spec.Offset previous)
    (offsetMember : offset ∈ (capability.offsetsAt previous).values) :
    spec.Compatible previous target offset := by
  let pair : spec.Target previous × spec.Offset previous := (target, offset)
  have pairMember : pair ∈ (capability.pairScheduleAt previous).values :=
    (Core.Finite.Enumeration.mem_product_values _ _ pair).mpr
      ⟨targetMember, offsetMember⟩
  obtain ⟨index, equal⟩ :=
    ((capability.pairScheduleAt previous).mem_iff_exists_index pair).mp
      pairMember
  by_contra incompatible
  exact state index (by simpa [equal, Incompatible] using incompatible)

end CompatibleState

/-- The selected predecessor-owned scale lies in the finite block regime. -/
structure FiniteScaleState (capability : Capability spec)
    (previous : Previous) : Prop where
  private mk ::
  finite : capability.scaleAt previous <= capability.scaleLimitAt previous

/-- The selected predecessor-owned scale lies in the orbit regime. -/
structure OrbitScaleState (capability : Capability spec)
    (previous : Previous) : Prop where
  private mk ::
  large : capability.scaleLimitAt previous < capability.scaleAt previous

namespace FiniteScaleState

/-- Package the finite inequality selected by Core's scale decision. -/
def ofBound {capability : Capability spec} {previous : Previous}
    (finite : capability.scaleAt previous <= capability.scaleLimitAt previous) :
    FiniteScaleState capability previous :=
  .mk finite

end FiniteScaleState

namespace OrbitScaleState

/-- Package the strict complementary inequality selected by Core. -/
def ofLarge {capability : Capability spec} {previous : Previous}
    (large : capability.scaleLimitAt previous < capability.scaleAt previous) :
    OrbitScaleState capability previous :=
  .mk large

end OrbitScaleState

/-- A finite-scale position survives exactly when its complete inherited
target-offset block scan has no hit. -/
def Survives (capability : Capability spec) (previous : Previous)
    (position : spec.Position previous (capability.scaleAt previous)) : Prop :=
  Core.Finite.Search.Avoids (capability.pairScheduleAt previous)
    (BlockHits capability previous position)

/-- The selected orbit slice avoids every target-offset pair in the inherited
schedule. -/
def OrbitAvoids (capability : Capability spec) (previous : Previous) : Prop :=
  Core.Finite.Search.Avoids (capability.pairScheduleAt previous)
    (OrbitHits capability previous)

end Hypostructure.CT17
