import Hypostructure.CT7.Capability
import Hypostructure.Core.Finite.Search

/-!
# CT7 generated states

All searchable carriers are the queried predecessor schedule.  The only
semantic promotion beyond that finite schedule is supplied by the registered
realization and symbolic-response coverage laws.
-/

namespace Hypostructure.CT7

universe uPrevious uRepresentative uContext uCoordinate uValue

variable {Previous : Type uPrevious}
  {spec : Spec.{uPrevious, uRepresentative, uContext, uCoordinate, uValue}
    Previous}

/-- Realization predicate on one exact residual-owned coordinate. -/
def ScheduledRealizes (capability : Capability spec) (previous : Previous)
    (coordinate : spec.system.Coordinate) : Prop :=
  spec.Realizes previous (capability.representativesAt previous).source
    (spec.system.decode coordinate)

/-- Canonical first realizing coordinate. -/
abbrev RealizationCertificate (capability : Capability spec)
    (previous : Previous) :=
  Core.Finite.Search.IndexedHit (capability.contextsAt previous)
    (ScheduledRealizes capability previous)

/-- Exhaustive absence of realization on the exact incoming schedule. -/
abbrev UnrealizedState (capability : Capability spec) (previous : Previous) :=
  Core.Finite.Search.Avoids (capability.contextsAt previous)
    (ScheduledRealizes capability previous)

namespace RealizationCertificate

/-- Exact scheduled coordinate selected by the canonical first-hit scan. -/
def coordinate {capability : Capability spec} {previous : Previous}
    (certificate : RealizationCertificate capability previous) :
    spec.system.Coordinate :=
  certificate.value

/-- Semantic context decoded from the selected coordinate. -/
def context {capability : Capability spec} {previous : Previous}
    (certificate : RealizationCertificate capability previous) :
    spec.system.Context :=
  spec.system.decode certificate.coordinate

/-- The selected coordinate belongs to the literal incoming schedule. -/
theorem scheduled {capability : Capability spec} {previous : Previous}
    (certificate : RealizationCertificate capability previous) :
    certificate.coordinate ∈ (capability.contextsAt previous).values :=
  certificate.member

/-- The selected semantic context realizes the left representative. -/
theorem realizes {capability : Capability spec} {previous : Previous}
    (certificate : RealizationCertificate capability previous) :
    spec.Realizes previous (capability.representativesAt previous).source
      certificate.context :=
  certificate.sound

end RealizationCertificate

namespace UnrealizedState

/-- Exhaustive scheduled failure plus registered coverage excludes realization
in every semantic context. -/
theorem noRealization {capability : Capability spec} {previous : Previous}
    (state : UnrealizedState capability previous) :
    forall context, Not (spec.Realizes previous
      (capability.representativesAt previous).source context) := by
  intro context realizes
  obtain ⟨index, scheduledRealizes⟩ :=
    capability.realizationCoverage previous context realizes
  exact state index scheduledRealizes

end UnrealizedState

/-- Exact response mismatch at one residual-owned coordinate. -/
def ResponseMismatch (capability : Capability spec) (previous : Previous)
    (coordinate : spec.system.Coordinate) : Prop :=
  spec.system.coordinateResponse
      (capability.representativesAt previous).source coordinate ≠
    spec.system.coordinateResponse
      (capability.representativesAt previous).replacement coordinate

/-- Core's exact response table over the queried schedule. -/
def responseTableAt (capability : Capability spec) (previous : Previous) :=
  Core.Response.FiniteTable.Table.build spec.system
    (capability.representativesAt previous)
    (capability.exactScheduleAt previous)

/-- Exhaustive response equality on the exact incoming schedule. -/
abbrev ResponseNeutralState (capability : Capability spec)
    (previous : Previous) :=
  Core.Finite.Search.Avoids (capability.contextsAt previous)
    (ResponseMismatch capability previous)

/-- Convert exact scan avoidance into Core's exact-table neutrality. -/
def finiteNeutralityOfAvoidance (capability : Capability spec)
    (previous : Previous) (state : ResponseNeutralState capability previous) :
    Core.Response.FiniteTable.Neutrality
      (responseTableAt capability previous) where
  equalAt := by
    intro index
    by_contra differs
    exact state index (by
      simpa [ResponseMismatch, responseTableAt, Capability.exactScheduleAt,
        Core.Finite.Enumeration.get] using differs)

/-- A concrete distinguishing semantic context, retained together with the
exhaustive preceding realization failure. -/
structure DistinguishingResidual (capability : Capability spec)
    (previous : Previous) where
  private mk ::
  unrealized : UnrealizedState capability previous
  distinction : Core.Finite.Search.IndexedHit
    (capability.contextsAt previous) (ResponseMismatch capability previous)

namespace DistinguishingResidual

/-- Package the exact Core search products. -/
def ofHit {capability : Capability spec} {previous : Previous}
    (unrealized : UnrealizedState capability previous)
    (distinction : Core.Finite.Search.IndexedHit
      (capability.contextsAt previous) (ResponseMismatch capability previous)) :
    DistinguishingResidual capability previous :=
  .mk unrealized distinction

/-- Selected residual-owned coordinate. -/
def coordinate {capability : Capability spec} {previous : Previous}
    (residual : DistinguishingResidual capability previous) :
    spec.system.Coordinate :=
  residual.distinction.value

/-- Selected semantic context. -/
def context {capability : Capability spec} {previous : Previous}
    (residual : DistinguishingResidual capability previous) :
    spec.system.Context :=
  spec.system.decode residual.coordinate

/-- The selected coordinate belongs to the exact incoming schedule. -/
theorem scheduled {capability : Capability spec} {previous : Previous}
    (residual : DistinguishingResidual capability previous) :
    residual.coordinate ∈ (capability.contextsAt previous).values :=
  residual.distinction.member

/-- Exact coordinate responses differ. -/
theorem differs {capability : Capability spec} {previous : Previous}
    (residual : DistinguishingResidual capability previous) :
    ResponseMismatch capability previous residual.coordinate :=
  residual.distinction.sound

/-- Exact semantic responses differ in the decoded context. -/
theorem contextDiffers {capability : Capability spec} {previous : Previous}
    (residual : DistinguishingResidual capability previous) :
    spec.system.contextResponse
        (capability.representativesAt previous).source residual.context ≠
      spec.system.contextResponse
        (capability.representativesAt previous).replacement residual.context := by
  intro equal
  exact residual.differs ((spec.system.coordinateExact
      (capability.representativesAt previous).source residual.coordinate).trans
    (equal.trans (spec.system.coordinateExact
      (capability.representativesAt previous).replacement
        residual.coordinate).symm))

/-- Realization has already failed in every semantic context. -/
theorem noRealization {capability : Capability spec} {previous : Previous}
    (residual : DistinguishingResidual capability previous) :
    forall context, Not (spec.Realizes previous
      (capability.representativesAt previous).source context) :=
  residual.unrealized.noRealization

end DistinguishingResidual

/-- Certified universal response neutrality after exhaustive realization and
distinction failure. -/
structure NeutralityCertificate (capability : Capability spec)
    (previous : Previous) where
  private mk ::
  unrealized : UnrealizedState capability previous
  finite : Core.Response.FiniteTable.Neutrality
    (responseTableAt capability previous)

namespace NeutralityCertificate

/-- Package exact avoidance results from both Core scans. -/
def ofAvoidance {capability : Capability spec} {previous : Previous}
    (unrealized : UnrealizedState capability previous)
    (neutral : ResponseNeutralState capability previous) :
    NeutralityCertificate capability previous :=
  .mk unrealized (finiteNeutralityOfAvoidance capability previous neutral)

/-- Realization is absent in every semantic context. -/
theorem noRealization {capability : Capability spec} {previous : Previous}
    (certificate : NeutralityCertificate capability previous) :
    forall context, Not (spec.Realizes previous
      (capability.representativesAt previous).source context) :=
  certificate.unrealized.noRealization

/-- Finite equality plus registered symbolic coverage yields universal exact
response neutrality without enumerating ambient contexts. -/
def universal {capability : Capability spec} {previous : Previous}
    (certificate : NeutralityCertificate capability previous) :
    Core.Response.UniversalNeutrality spec.system
      (capability.representativesAt previous) :=
  certificate.finite.universal (capability.responseCoverage previous)

/-- Universal response neutrality transports any separately registered exact
target semantics. -/
def targetComplete {capability : Capability spec} {previous : Previous}
    (certificate : NeutralityCertificate capability previous)
    (semantics : Core.Response.TargetSemantics spec.system) :
    Core.Response.TargetCompleteEquivalence semantics
      (capability.representativesAt previous) :=
  certificate.universal.targetComplete semantics

end NeutralityCertificate

end Hypostructure.CT7
