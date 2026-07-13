import StructuralExhaustion.CT7.Capability

namespace StructuralExhaustion.CT7

variable {P : Core.Problem} (S : Spec P) (capability : Capability S)
variable (ctx : Core.BranchContext P) (input : Input S ctx)

/-- A concrete realizing context; realization is searched before distinction. -/
structure RealizationCertificate where
  context : S.Context
  member : context ∈ (capability.contexts ctx input.left input.right).orderedValues
  realizes : S.Realizes ctx input.left context

/-- Exhaustive absence of a realizing context. -/
structure UnrealizedState : Prop where
  complete : ∀ context,
    context ∈ (capability.contexts ctx input.left input.right).orderedValues
  noRealization : ∀ context, ¬ S.Realizes ctx input.left context

/-- A concrete exact response mismatch. -/
structure DistinguishingResidual where
  unrealized : UnrealizedState S capability ctx input
  context : S.Context
  differs : S.response ctx input.left context ≠ S.response ctx input.right context

/-- Exact contextual neutrality over the complete context enumeration. -/
structure NeutralityCertificate : Prop where
  unrealized : UnrealizedState S capability ctx input
  allEqual : ∀ context,
    S.response ctx input.left context = S.response ctx input.right context

end StructuralExhaustion.CT7
