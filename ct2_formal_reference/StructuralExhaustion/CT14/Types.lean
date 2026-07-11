import StructuralExhaustion.CT9.Interface
import StructuralExhaustion.CT10.Interface
import StructuralExhaustion.CT14.Interface

namespace StructuralExhaustion.CT14

/-! Proof-carrying vocabulary for CT14 aggregate closure. -/

structure Framework where
  entry : Interface.Framework
  ct9 : CT9.Interface.Framework
  ct10 : CT10.Interface.Framework
  LowerBoundCertified : Interface.Input entry → Prop
  UpperBoundCertified : Interface.Input entry → Prop
  MultiplicityCounted : Interface.Input entry → Prop
  AggregateComparison : Interface.Input entry → Prop
  CT9Aligned : Interface.Input entry → CT9.Interface.Input ct9 → Prop
  CT10Aligned : Interface.Input entry → CT10.Interface.Input ct10 → Prop

abbrev Input (F : Framework) := Interface.Input F.entry
def ScopeReadyAt (F : Framework) (input : Input F) : Prop :=
  Interface.ScopeReadyAt F.entry input
structure ScopeCandidate (F : Framework) (input : Input F) : Prop where
  unavailable : ¬ ScopeReadyAt F input
structure ScopedState (F : Framework) (input : Input F) : Prop where
  ready : ScopeReadyAt F input
structure BoundsState (F : Framework) (input : Input F) : Prop where
  scope : ScopedState F input
  lower : F.LowerBoundCertified input
  upper : F.UpperBoundCertified input
structure MultiplicityState (F : Framework) (input : Input F)
    (_bounds : BoundsState F input) : Prop where
  counted : F.MultiplicityCounted input
structure C4Certificate (F : Framework) (input : Input F)
    {bounds : BoundsState F input} (_multiplicity : MultiplicityState F input bounds) : Prop where
  comparison : F.AggregateComparison input
  closes : F.entry.C4Claim input.G input.branch
structure CT9Payload (F : Framework) (input : Input F)
    (_bounds : BoundsState F input) where
  downstream : CT9.Interface.Input F.ct9
  aligned : F.CT9Aligned input downstream
structure CT10Payload (F : Framework) (input : Input F)
    (_bounds : BoundsState F input) where
  downstream : CT10.Interface.Input F.ct10
  aligned : F.CT10Aligned input downstream
namespace CT9Payload
def toInput {F : Framework} {input : Input F} {bounds : BoundsState F input}
    (payload : CT9Payload F input bounds) : CT9.Interface.Input F.ct9 := payload.downstream
end CT9Payload
namespace CT10Payload
def toInput {F : Framework} {input : Input F} {bounds : BoundsState F input}
    (payload : CT10Payload F input bounds) : CT10.Interface.Input F.ct10 := payload.downstream
end CT10Payload
inductive HandoffPayload (F : Framework) (input : Input F) where
  | ct9 {bounds : BoundsState F input} (payload : CT9Payload F input bounds)
  | ct10 {bounds : BoundsState F input} (payload : CT10Payload F input bounds)
structure Port (F : Framework) (input : Input F) where
  accepts : HandoffPayload F input → Prop
structure HandoffPlan (F : Framework) (input : Input F) (port : Port F input) where
  accept : ∀ payload : HandoffPayload F input, port.accepts payload

end StructuralExhaustion.CT14
