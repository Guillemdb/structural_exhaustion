import StructuralExhaustion.CT1.Spec
import StructuralExhaustion.Core.AutomationFirst

namespace StructuralExhaustion.CT1

/-- Number of primitive realization decisions made by the exhaustive CT1
schedule when every finite fibre is inspected.  This counts only the local
tests supplied by the capability; it does not construct any ambient universe. -/
def searchCheckBound {P : Core.Problem} (S : Spec P)
    (tests : FinEnum S.TestIndex)
    (witnesses :
      (G : P.Ambient) →
      (index : S.TestIndex) →
      FinEnum (S.Witness G index))
    (G : P.Ambient) : Nat :=
  (tests.orderedValues.map fun index =>
    (witnesses G index).orderedValues.length).sum

/-- The complete problem-specific surface needed to execute CT1.

The capability contains only finite enumerators and a decision procedure for
the primitive realization relation. Search, exhaustiveness, certificates,
paths, and terminal selection are framework-derived. -/
structure Capability {P : Core.Problem} (S : Spec P) where
  tests : FinEnum S.TestIndex
  witnesses :
    (G : P.Ambient) →
    (index : S.TestIndex) →
    FinEnum (S.Witness G index)
  realizesDecidable :
    (G : P.Ambient) →
    (index : S.TestIndex) →
    (witness : S.Witness G index) →
    Decidable (S.Realizes G index witness)
  /-- Application-specific input size used to audit the local CT1 schedule. -/
  inputSize : P.Ambient → Nat
  /-- Coefficient in the certified polynomial work bound. -/
  workCoefficient : Nat
  /-- Degree in the certified polynomial work bound. -/
  workDegree : Nat
  /-- The complete local schedule is polynomial in the declared input size. -/
  workBound : ∀ G,
    searchCheckBound S tests witnesses G ≤
      workCoefficient * (inputSize G + 1) ^ workDegree

namespace Capability

/-- The machine-checkable polynomial bound carried by every exhaustive CT1
capability. -/
def polynomialBudget {P : Core.Problem} {S : Spec P}
    (capability : Capability S) :
    Core.PolynomialCheckBudget P.Ambient where
  size := capability.inputSize
  checks := searchCheckBound S capability.tests capability.witnesses
  coefficient := capability.workCoefficient
  degree := capability.workDegree
  bounded := capability.workBound

/-- CT1 consumes an inherited branch and requires no route-specific seed. -/
def tacticInterface {P : Core.Problem} {S : Spec P}
    (_capability : Capability S) : Core.Routing.TacticInterface where
  Context := Core.BranchContext P
  Trigger := fun _ => Unit

end Capability

end StructuralExhaustion.CT1
