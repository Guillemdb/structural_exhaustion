import Hypostructure.Core.Response.System

/-!
# CT7 exact-context specification

CT7 first asks whether the left representative realizes the active target in
one residual-owned context.  Only after exhaustive failure does it compare
the two representatives' exact responses on that same context schedule.
-/

namespace Hypostructure.CT7

universe uPrevious uRepresentative uContext uCoordinate uValue

/-- Domain-neutral semantics for exact context classification. -/
structure Spec (Previous : Type uPrevious) where
  Representative : Type uRepresentative
  system : Core.Response.System.{uRepresentative, uContext, uCoordinate,
    uValue} Representative
  Realizes : Previous -> Representative -> system.Context -> Prop

end Hypostructure.CT7
