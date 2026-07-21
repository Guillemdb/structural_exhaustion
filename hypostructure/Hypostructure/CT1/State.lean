import Hypostructure.CT1.Capability
import Hypostructure.Core.Finite.Search

/-!
# CT1 proof states

Successful and avoiding states are the generic finite-search certificates
specialized to the incoming CT1 schedule.  CT1 does not introduce a parallel
certificate model.
-/

namespace Hypostructure.CT1

universe uPrevious uCandidate

/-- Framework-produced first validated candidate. -/
abbrev C1Certificate {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uCandidate} Previous}
    (capability : Capability spec) (previous : Previous) :=
  Core.Finite.Search.IndexedHit (capability.scheduleAt previous)
    (spec.Realizes previous)

/-- Framework-produced exhaustive failure on the exact incoming schedule. -/
abbrev AvoidingState {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uCandidate} Previous}
    (capability : Capability spec) (previous : Previous) :=
  Core.Finite.Search.Avoids (capability.scheduleAt previous)
    (spec.Realizes previous)

namespace C1Certificate

/-- The first-hit certificate realizes the exact scheduled target. -/
theorem target {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uCandidate} Previous}
    {capability : Capability spec} {previous : Previous}
    (certificate : C1Certificate capability previous) :
    Target spec previous (capability.scheduleAt previous) :=
  ⟨certificate.value, certificate.member, certificate.sound⟩

end C1Certificate

namespace AvoidingState

/-- Exhaustive indexed avoidance excludes every member of the exact schedule. -/
theorem noRealization {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uCandidate} Previous}
    {capability : Capability spec} {previous : Previous}
    (state : AvoidingState capability previous) :
    forall candidate,
      candidate ∈ (capability.scheduleAt previous).values ->
        Not (spec.Realizes previous candidate) := by
  intro candidate member realizes
  obtain ⟨index, equal⟩ :=
    ((capability.scheduleAt previous).mem_iff_exists_index candidate).mp member
  exact state index (by simpa [equal] using realizes)

/-- Exact schedule exhaustion is CT1 target avoidance. -/
theorem targetAvoiding {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uCandidate} Previous}
    {capability : Capability spec} {previous : Previous}
    (state : AvoidingState capability previous) :
    Not (Target spec previous (capability.scheduleAt previous)) := by
  rintro ⟨candidate, member, realizes⟩
  exact state.noRealization candidate member realizes

end AvoidingState

end Hypostructure.CT1
