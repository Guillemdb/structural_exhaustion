import Lean

namespace StructuralExhaustion.Canonical

/-- Human-facing documentation attached to one required capability declaration.
The mathematical definition is LaTeX source; it is documentation anchored to,
but not proved equivalent to, the compiled Lean declaration. -/
structure CapabilityConceptPresentation where
  label : String
  mathematicalDefinition : String
  plainExplanation : String
  deriving Repr, DecidableEq

/-- Lean-owned semantic metadata for one distinct required definition in a
capability contract.  `requirementRef` is the stable spelling used by the
contract, while `declarationName` is the fully resolved compiled Lean name. -/
structure CapabilityConcept where
  conceptId : String
  requirementRef : String
  declarationName : Lean.Name
  presentation : CapabilityConceptPresentation
  deriving Repr, DecidableEq

/-- Concise constructor used by the CT metadata registry. -/
def capabilityConcept
    (conceptId requirementRef : String)
    (declarationName : Lean.Name)
    (label mathematicalDefinition plainExplanation : String) :
    CapabilityConcept := {
  conceptId := conceptId
  requirementRef := requirementRef
  declarationName := declarationName
  presentation := {
    label := label
    mathematicalDefinition := mathematicalDefinition
    plainExplanation := plainExplanation
  }
}

end StructuralExhaustion.Canonical
