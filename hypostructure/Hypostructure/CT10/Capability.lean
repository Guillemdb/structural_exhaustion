import Hypostructure.CT10.Spec
import Hypostructure.Core.Budget.Work
import Hypostructure.Core.Residual.Query

/-!
# CT10 executable capability

The datum and complete class schedules are reads from the exact predecessor
ledger.  CT10 derives row observations, searches, promotion, routing, and work
from those two queries.
-/

namespace Hypostructure.CT10

universe uPrevious uDatum uClass uPromotion

/-- Worst-case primitive checks: one direct test per class followed, when
needed, by one complete datum scan per class. -/
def localCheckBound {Previous : Type uPrevious}
    (spec : Spec.{uPrevious, uDatum, uClass, uPromotion} Previous)
    (data : Core.Residual.Query Previous fun previous =>
      Core.Finite.Enumeration (spec.Datum previous))
    (classes : Core.Residual.Query Previous fun previous =>
      Core.Finite.CompleteEnumeration (spec.Class previous))
    (previous : Previous) : Nat :=
  let classCount := (classes.read previous).toEnumeration.card
  let datumCount := (data.read previous).card
  classCount + classCount * datumCount

/-- Minimal author surface for executable CT10 classification. -/
structure Capability {Previous : Type uPrevious}
    (spec : Spec.{uPrevious, uDatum, uClass, uPromotion} Previous) where
  data : Core.Residual.Query Previous fun previous =>
    Core.Finite.Enumeration (spec.Datum previous)
  classes : Core.Residual.Query Previous fun previous =>
    Core.Finite.CompleteEnumeration (spec.Class previous)
  directDecidable : (previous : Previous) ->
    (cls : spec.Class previous) -> Decidable (spec.Direct previous cls)
  inputSize : Previous -> Nat
  workCoefficient : Nat
  workDegree : Nat
  workBound : forall previous,
    localCheckBound spec data classes previous <=
      workCoefficient * (inputSize previous + 1) ^ workDegree

namespace Capability

/-- Exact residual-owned datum schedule. -/
def dataAt {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uDatum, uClass, uPromotion} Previous}
    (capability : Capability spec) (previous : Previous) :
    Core.Finite.Enumeration (spec.Datum previous) :=
  capability.data.read previous

/-- Exact residual-owned complete class schedule. -/
def completeClassesAt {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uDatum, uClass, uPromotion} Previous}
    (capability : Capability spec) (previous : Previous) :
    Core.Finite.CompleteEnumeration (spec.Class previous) :=
  capability.classes.read previous

/-- Ordered class scan extracted without changing the residual-owned table. -/
def classesAt {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uDatum, uClass, uPromotion} Previous}
    (capability : Capability spec) (previous : Previous) :
    Core.Finite.Enumeration (spec.Class previous) :=
  (capability.completeClassesAt previous).toEnumeration

/-- Framework-visible polynomial envelope for a complete CT10 run. -/
def polynomialBudget {Previous : Type uPrevious}
    {spec : Spec.{uPrevious, uDatum, uClass, uPromotion} Previous}
    (capability : Capability spec) :
    Core.PolynomialCheckBudget Previous where
  size := capability.inputSize
  checks := localCheckBound spec capability.data capability.classes
  coefficient := capability.workCoefficient
  degree := capability.workDegree
  bounded := capability.workBound

end Capability

end Hypostructure.CT10
