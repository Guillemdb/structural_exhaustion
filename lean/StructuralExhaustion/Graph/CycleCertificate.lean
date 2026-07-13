import StructuralExhaustion.CT1.TargetEncoding
import StructuralExhaustion.Graph.Cycle
import StructuralExhaustion.Graph.FiniteObject

namespace StructuralExhaustion.Graph

open StructuralExhaustion

universe uAmbient uBranch uVertex

/-!
# Certificate-driven CT1 cycle targets

The graph layer validates an explicitly constructed Mathlib cycle.  It never
enumerates walks, supports, vertex lists, or ambient graphs.
-/

/-- Local CT1 encoding for a cycle-length target.  The code is the concrete
Mathlib cycle certificate itself and acceptance is definitional. -/
def cycleTargetCertificateEncoding
    {P : Core.Problem.{uAmbient, uBranch}}
    {V : Type uVertex}
    (objectOf : P.Ambient → FiniteObject V)
    (LengthOK : Nat → Prop) :
    CT1.TargetCertificateEncoding (fun ambient =>
      HasCycleWithLength (objectOf ambient).graph LengthOK) where
  Code := fun ambient => CycleWithLength (objectOf ambient).graph LengthOK
  Accepts := fun _ambient _cycle => True
  encode := by
    rintro ambient ⟨cycle⟩
    exact ⟨cycle, trivial⟩
  decode := by
    intro ambient cycle _accepted
    exact ⟨cycle⟩

end StructuralExhaustion.Graph
