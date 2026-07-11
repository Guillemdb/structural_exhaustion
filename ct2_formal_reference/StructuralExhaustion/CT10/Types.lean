import StructuralExhaustion.CT3.Types
import StructuralExhaustion.CT7.Interface
import StructuralExhaustion.CT10.Interface
import StructuralExhaustion.CT15.Interface

namespace StructuralExhaustion.CT10

/-! Proof-carrying vocabulary for CT10 finite-label refinement. -/

structure Framework where
  entry : Interface.Framework
  ct3 : CT3.Framework
  ct7 : CT7.Interface.Framework
  ct15 : CT15.Interface.Framework

  LabelClassesExhaust : Interface.Input entry → Prop
  ExchangeSupportFinite : Interface.Input entry → Prop
  DirectClassified : Interface.Input entry → Prop
  MissingDatumExtracted : Interface.Input entry → Prop
  PromotionCertified : Interface.Input entry → Prop

  CT3Aligned : Interface.Input entry → CT3.Input ct3 → Prop
  CT7Aligned : Interface.Input entry → CT7.Interface.Input ct7 → Prop
  CT15Aligned : Interface.Input entry → CT15.Interface.Input ct15 → Prop

abbrev Input (F : Framework) := Interface.Input F.entry
def ScopeReadyAt (F : Framework) (input : Input F) : Prop :=
  Interface.ScopeReadyAt F.entry input

structure ScopeCandidate (F : Framework) (input : Input F) : Prop where
  unavailable : ¬ ScopeReadyAt F input
structure ScopedState (F : Framework) (input : Input F) : Prop where
  ready : ScopeReadyAt F input

structure LabelCertificate (F : Framework) (input : Input F) : Prop where
  exhaustive : F.LabelClassesExhaust input
  finiteSupport : F.ExchangeSupportFinite input
structure LabelState (F : Framework) (input : Input F) : Prop where
  scope : ScopedState F input
  certificate : LabelCertificate F input

structure C5Certificate (F : Framework) (input : Input F)
    (_labels : LabelState F input) : Prop where
  closes : F.entry.C5Claim input.G input.branch

structure DirectState (F : Framework) (input : Input F)
    (_labels : LabelState F input) : Prop where
  classified : F.DirectClassified input

structure MissingState (F : Framework) (input : Input F)
    (_labels : LabelState F input) : Prop where
  extracted : F.MissingDatumExtracted input

structure PromotedState (F : Framework) (input : Input F)
    {labels : LabelState F input}
    (_missing : MissingState F input labels) : Prop where
  certified : F.PromotionCertified input

/-- Direct class-response route to CT3. -/
structure DirectCT3Payload (F : Framework) (input : Input F)
    {labels : LabelState F input}
    (_direct : DirectState F input labels) where
  downstream : CT3.Input F.ct3
  aligned : F.CT3Aligned input downstream

/-- CT3 response data obtained only after promotion of a missing invariant. -/
structure PromotedCT3Payload (F : Framework) (input : Input F)
    {labels : LabelState F input}
    {missing : MissingState F input labels}
    (_promoted : PromotedState F input missing) where
  downstream : CT3.Input F.ct3
  aligned : F.CT3Aligned input downstream

/-- The consumer port sees one CT3 payload family, while each constructor
retains the exact state that licensed its route. -/
inductive CT3Payload (F : Framework) (input : Input F) where
  | direct {labels : LabelState F input}
      {direct : DirectState F input labels}
      (payload : DirectCT3Payload F input direct)
  | promoted {labels : LabelState F input}
      {missing : MissingState F input labels}
      {promoted : PromotedState F input missing}
      (payload : PromotedCT3Payload F input promoted)

namespace CT3Payload
def toInput {F : Framework} {input : Input F} :
    CT3Payload F input → CT3.Input F.ct3
  | .direct payload => payload.downstream
  | .promoted payload => payload.downstream
end CT3Payload

structure CT7Payload (F : Framework) (input : Input F)
    {labels : LabelState F input}
    (_direct : DirectState F input labels) where
  downstream : CT7.Interface.Input F.ct7
  aligned : F.CT7Aligned input downstream

structure CT15Payload (F : Framework) (input : Input F)
    {labels : LabelState F input}
    {missing : MissingState F input labels}
    (_promoted : PromotedState F input missing) where
  downstream : CT15.Interface.Input F.ct15
  aligned : F.CT15Aligned input downstream

namespace CT7Payload
def toInput {F : Framework} {input : Input F} {labels : LabelState F input}
    {direct : DirectState F input labels} (payload : CT7Payload F input direct) :
    CT7.Interface.Input F.ct7 := payload.downstream
end CT7Payload

namespace CT15Payload
def toInput {F : Framework} {input : Input F} {labels : LabelState F input}
    {missing : MissingState F input labels} {promoted : PromotedState F input missing}
    (payload : CT15Payload F input promoted) : CT15.Interface.Input F.ct15 :=
  payload.downstream
end CT15Payload

inductive HandoffPayload (F : Framework) (input : Input F) where
  | ct3 (payload : CT3Payload F input)
  | ct7 {labels : LabelState F input} {direct : DirectState F input labels}
      (payload : CT7Payload F input direct)
  | ct15 {labels : LabelState F input} {missing : MissingState F input labels}
      {promoted : PromotedState F input missing}
      (payload : CT15Payload F input promoted)

structure Port (F : Framework) (input : Input F) where
  accepts : HandoffPayload F input → Prop
structure HandoffPlan (F : Framework) (input : Input F) (port : Port F input) where
  accept : ∀ payload : HandoffPayload F input, port.accepts payload

end StructuralExhaustion.CT10
