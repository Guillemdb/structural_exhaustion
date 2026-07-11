import StructuralExhaustion.CT4.Types
import StructuralExhaustion.CT7.Interface
import StructuralExhaustion.CT8.Interface
import StructuralExhaustion.CT9.Interface
import StructuralExhaustion.CT10.Interface

namespace StructuralExhaustion.CT9

/-! Proof-carrying vocabulary for CT9 overload exhaustion. -/

structure Framework where
  entry : Interface.Framework
  ct4 : CT4.Framework
  ct7 : CT7.Interface.Framework
  ct8 : CT8.Interface.Framework
  ct10 : CT10.Interface.Framework

  FibreCertified : Interface.Input entry → Prop
  LabelsTooCoarse : Interface.Input entry → Prop
  BoundedMultiplicity : Interface.Input entry → Prop
  Overloaded : Interface.Input entry → Prop
  HomogeneousExtraction : Interface.Input entry → Prop

  CT4Aligned : Interface.Input entry → CT4.Input ct4 → Prop
  CT7Aligned : Interface.Input entry → CT7.Interface.Input ct7 → Prop
  CT8Aligned : Interface.Input entry → CT8.Interface.Input ct8 → Prop
  CT10Aligned : Interface.Input entry → CT10.Interface.Input ct10 → Prop

abbrev Input (F : Framework) := Interface.Input F.entry
def ScopeReadyAt (F : Framework) (input : Input F) : Prop :=
  Interface.ScopeReadyAt F.entry input

structure ScopeCandidate (F : Framework) (input : Input F) : Prop where
  unavailable : ¬ ScopeReadyAt F input
structure ScopedState (F : Framework) (input : Input F) : Prop where
  ready : ScopeReadyAt F input

structure CT10Payload (F : Framework) (input : Input F) where
  coarse : F.LabelsTooCoarse input
  downstream : CT10.Interface.Input F.ct10
  aligned : F.CT10Aligned input downstream

structure FibreCertificate (F : Framework) (input : Input F) : Prop where
  certified : F.FibreCertified input
structure FibreState (F : Framework) (input : Input F) : Prop where
  scope : ScopedState F input
  certificate : FibreCertificate F input

structure CT4Payload (F : Framework) (input : Input F)
    (_fibre : FibreState F input) where
  bounded : F.BoundedMultiplicity input
  downstream : CT4.Input F.ct4
  aligned : F.CT4Aligned input downstream

structure OverloadedState (F : Framework) (input : Input F)
    (_fibre : FibreState F input) : Prop where
  overloaded : F.Overloaded input

structure ExtractionCertificate (F : Framework) (input : Input F)
    {fibre : FibreState F input}
    (_overloaded : OverloadedState F input fibre) : Prop where
  homogeneous : F.HomogeneousExtraction input
structure ExtractionState (F : Framework) (input : Input F)
    {fibre : FibreState F input}
    (overloaded : OverloadedState F input fibre) : Prop where
  certificate : ExtractionCertificate F input overloaded

structure C1Certificate (F : Framework) (input : Input F)
    {fibre : FibreState F input}
    {overloaded : OverloadedState F input fibre}
    (_extraction : ExtractionState F input overloaded) : Prop where
  closes : F.entry.C1Claim input.G input.branch

structure CT7Payload (F : Framework) (input : Input F)
    {fibre : FibreState F input}
    {overloaded : OverloadedState F input fibre}
    (_extraction : ExtractionState F input overloaded) where
  downstream : CT7.Interface.Input F.ct7
  aligned : F.CT7Aligned input downstream

structure CT8Payload (F : Framework) (input : Input F)
    {fibre : FibreState F input}
    {overloaded : OverloadedState F input fibre}
    (_extraction : ExtractionState F input overloaded) where
  downstream : CT8.Interface.Input F.ct8
  aligned : F.CT8Aligned input downstream

namespace CT10Payload
def toInput {F : Framework} {input : Input F} (payload : CT10Payload F input) :
    CT10.Interface.Input F.ct10 := payload.downstream
end CT10Payload
namespace CT4Payload
def toInput {F : Framework} {input : Input F} {fibre : FibreState F input}
    (payload : CT4Payload F input fibre) : CT4.Input F.ct4 := payload.downstream
end CT4Payload
namespace CT7Payload
def toInput {F : Framework} {input : Input F} {fibre : FibreState F input}
    {overloaded : OverloadedState F input fibre}
    {extraction : ExtractionState F input overloaded}
    (payload : CT7Payload F input extraction) : CT7.Interface.Input F.ct7 := payload.downstream
end CT7Payload
namespace CT8Payload
def toInput {F : Framework} {input : Input F} {fibre : FibreState F input}
    {overloaded : OverloadedState F input fibre}
    {extraction : ExtractionState F input overloaded}
    (payload : CT8Payload F input extraction) : CT8.Interface.Input F.ct8 := payload.downstream
end CT8Payload

inductive HandoffPayload (F : Framework) (input : Input F) where
  | ct10 (payload : CT10Payload F input)
  | ct4 {fibre : FibreState F input} (payload : CT4Payload F input fibre)
  | ct7 {fibre : FibreState F input}
      {overloaded : OverloadedState F input fibre}
      {extraction : ExtractionState F input overloaded}
      (payload : CT7Payload F input extraction)
  | ct8 {fibre : FibreState F input}
      {overloaded : OverloadedState F input fibre}
      {extraction : ExtractionState F input overloaded}
      (payload : CT8Payload F input extraction)

structure Port (F : Framework) (input : Input F) where
  accepts : HandoffPayload F input → Prop
structure HandoffPlan (F : Framework) (input : Input F) (port : Port F input) where
  accept : ∀ payload : HandoffPayload F input, port.accepts payload

end StructuralExhaustion.CT9
