import Hypostructure.CT10.Capability
import Hypostructure.Core.Finite.Search

/-!
# CT10 semantic states

Rows are propositions over the exact incoming datum schedule.  No filtered
subtype, image, replacement carrier, or node-local enumeration is created.
-/

namespace Hypostructure.CT10

universe uPrevious uDatum uClass uPromotion

variable {Previous : Type uPrevious}
  {spec : Spec.{uPrevious, uDatum, uClass, uPromotion} Previous}

/-- One datum belongs to a class according to the application classifier. -/
def InClass (spec : Spec.{uPrevious, uDatum, uClass, uPromotion} Previous)
    (previous : Previous) (cls : spec.Class previous)
    (datum : spec.Datum previous) : Prop :=
  spec.classOf previous datum = cls

/-- A class is observed by at least one member of the exact incoming data. -/
def Observed (capability : Capability spec) (previous : Previous)
    (cls : spec.Class previous) : Prop :=
  Exists fun datum => datum ∈ (capability.dataAt previous).values ∧
    InClass spec previous cls datum

/-- The exact complementary row state used by first-missing search. -/
def Missing (capability : Capability spec) (previous : Previous)
    (cls : spec.Class previous) : Prop :=
  Not (Observed capability previous cls)

/-- Framework-produced first direct class in residual schedule order. -/
abbrev DirectResidual (capability : Capability spec) (previous : Previous) :=
  Core.Finite.Search.IndexedHit (capability.classesAt previous)
    (spec.Direct previous)

/-- Framework-produced first unobserved class in residual schedule order. -/
abbrev MissingDatum (capability : Capability spec) (previous : Previous) :=
  Core.Finite.Search.IndexedHit (capability.classesAt previous)
    (Missing capability previous)

/-- Exhaustive direct-case absence on the declared complete class universe. -/
abbrev DirectAbsent (capability : Capability spec) (previous : Previous) :=
  Core.Finite.Search.Avoids (capability.classesAt previous)
    (spec.Direct previous)

/-- Every declared class survives first-missing search. -/
abbrev NoMissingClass (capability : Capability spec) (previous : Previous) :=
  Core.Finite.Search.Avoids (capability.classesAt previous)
    (Missing capability previous)

end Hypostructure.CT10
