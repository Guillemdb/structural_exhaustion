import StructuralExhaustion.CT2.Types

namespace StructuralExhaustion.CT2.Nodes.Context

inductive Decision (F : Framework) (input : Input F)
    (state : CandidateState F input) where
  | certified
      (certificate : CandidateContextCertificate F input state)
  | residual (payload : ContextCT3Payload F input state)

abbrev Contract (F : Framework) (input : Input F)
    (state : CandidateState F input) := Decision F input state

structure Plan (F : Framework) (input : Input F) where
  certify : ∀ state : CandidateState F input, Decision F input state

def run {F : Framework} {input : Input F}
    (plan : Plan F input) (state : CandidateState F input) :
    Contract F input state :=
  plan.certify state

@[simp] theorem run_eq_certify {F : Framework} {input : Input F}
    (plan : Plan F input) (state : CandidateState F input) :
    run plan state = plan.certify state := rfl

theorem certified_residual_disjoint {F : Framework} {input : Input F}
    {state : CandidateState F input}
    (certificate : CandidateContextCertificate F input state)
    (payload : ContextCT3Payload F input state) : False :=
  payload.residual.notProfilePreserved certificate.profilePreserved

end StructuralExhaustion.CT2.Nodes.Context
