import StructuralExhaustion.CT3.Types
import StructuralExhaustion.CT10.Interface
import StructuralExhaustion.CT16.Interface

namespace StructuralExhaustion.CT16

/-! Proof-carrying vocabulary for CT16 whole-object exact types. -/

structure Framework where
  entry : Interface.Framework
  ct3 : CT3.Framework
  ct10 : CT10.Interface.Framework
  ProperSupport : Interface.Input entry → Prop
  WholeSupport : Interface.Input entry → Prop
  ClosedTypeComputed : Interface.Input entry → Prop
  NoSilentIdentification : Interface.Input entry → Prop
  LiteralEquality : Interface.Input entry → Prop
  CT3Aligned : Interface.Input entry → CT3.Input ct3 → Prop
  CT10Aligned : Interface.Input entry → CT10.Interface.Input ct10 → Prop

abbrev Input (F : Framework) := Interface.Input F.entry
def ScopeReadyAt (F : Framework) (input : Input F) : Prop := Interface.ScopeReadyAt F.entry input
structure ScopeCandidate (F : Framework) (input : Input F) : Prop where
  unavailable : ¬ ScopeReadyAt F input
structure ProperState (F : Framework) (input : Input F) : Prop where proper : F.ProperSupport input
structure WholeState (F : Framework) (input : Input F) : Prop where whole : F.WholeSupport input
structure ScopedState (F : Framework) (input : Input F)
    (_whole : WholeState F input) : Prop where ready : ScopeReadyAt F input
structure ClosedTypeState (F : Framework) (input : Input F)
    {whole : WholeState F input} (_scope : ScopedState F input whole) : Prop where
  computed : F.ClosedTypeComputed input
  exact : F.NoSilentIdentification input
structure C2Certificate (F : Framework) (input : Input F)
    {whole : WholeState F input} {scope : ScopedState F input whole}
    (_closed : ClosedTypeState F input scope) : Prop where
  equal : F.LiteralEquality input
  closes : F.entry.C2Claim input.G input.branch
structure CT3Payload (F : Framework) (input : Input F) (_proper : ProperState F input) where
  downstream : CT3.Input F.ct3
  aligned : F.CT3Aligned input downstream
structure CT10Payload (F : Framework) (input : Input F)
    {whole : WholeState F input} {scope : ScopedState F input whole}
    (_closed : ClosedTypeState F input scope) where
  downstream : CT10.Interface.Input F.ct10
  aligned : F.CT10Aligned input downstream
namespace CT3Payload
def toInput {F : Framework} {input : Input F} {proper : ProperState F input}
    (p : CT3Payload F input proper) : CT3.Input F.ct3 := p.downstream
end CT3Payload
namespace CT10Payload
def toInput {F : Framework} {input : Input F} {whole : WholeState F input}
    {scope : ScopedState F input whole} {closed : ClosedTypeState F input scope}
    (p : CT10Payload F input closed) : CT10.Interface.Input F.ct10 := p.downstream
end CT10Payload
inductive HandoffPayload (F : Framework) (input : Input F) where
  | ct3 {proper : ProperState F input} (payload : CT3Payload F input proper)
  | ct10 {whole : WholeState F input} {scope : ScopedState F input whole}
      {closed : ClosedTypeState F input scope} (payload : CT10Payload F input closed)
structure Port (F : Framework) (input : Input F) where accepts : HandoffPayload F input → Prop
structure HandoffPlan (F : Framework) (input : Input F) (port : Port F input) where
  accept : ∀ payload : HandoffPayload F input, port.accepts payload

end StructuralExhaustion.CT16
