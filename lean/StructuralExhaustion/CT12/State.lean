import StructuralExhaustion.CT12.Capability

namespace StructuralExhaustion.CT12

universe uAmbient uBranch uState uPeeled uDemand uTier
variable {P : Core.Problem.{uAmbient, uBranch}}
variable (capability : Capability.{uAmbient, uBranch, uState, uPeeled, uDemand, uTier} P)

structure ExhaustedCertificate where
  state : capability.State 0

end StructuralExhaustion.CT12
