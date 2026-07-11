import StructuralExhaustion.CT3.Types
import StructuralExhaustion.CT8.Interface
import StructuralExhaustion.CT10.Interface
import StructuralExhaustion.CT14.Interface
import StructuralExhaustion.CT17.Interface

namespace StructuralExhaustion.CT17

/-! Proof-carrying vocabulary for CT17 target thickening. -/

structure Framework where
  entry : Interface.Framework
  ct3 : CT3.Framework
  ct8 : CT8.Interface.Framework
  ct10 : CT10.Interface.Framework
  ct14 : CT14.Interface.Framework
  CompatibleOffsets : Interface.Input entry → Prop
  BlockCertified : Interface.Input entry → Prop
  FiniteRange : Interface.Input entry → Prop
  RepeatedIncrements : Interface.Input entry → Prop
  NoFiniteSurvivors : Interface.Input entry → Prop
  ArithmeticForcesTarget : Interface.Input entry → Prop
  CT3Aligned : Interface.Input entry → CT3.Input ct3 → Prop
  CT8Aligned : Interface.Input entry → CT8.Interface.Input ct8 → Prop
  CT10Aligned : Interface.Input entry → CT10.Interface.Input ct10 → Prop
  CT14Aligned : Interface.Input entry → CT14.Interface.Input ct14 → Prop

abbrev Input (F : Framework) := Interface.Input F.entry
def ScopeReadyAt (F : Framework) (input : Input F) : Prop := Interface.ScopeReadyAt F.entry input
structure ScopeCandidate (F : Framework) (input : Input F) : Prop where
  unavailable : ¬ ScopeReadyAt F input
structure ScopedState (F : Framework) (input : Input F) : Prop where ready : ScopeReadyAt F input
structure CompatibleState (F : Framework) (input : Input F)
    (_scope : ScopedState F input) : Prop where compatible : F.CompatibleOffsets input
structure IncompatibleState (F : Framework) (input : Input F)
    (_scope : ScopedState F input) : Prop where incompatible : ¬ F.CompatibleOffsets input
structure BlockState (F : Framework) (input : Input F)
    {scope : ScopedState F input} (_compatible : CompatibleState F input scope) : Prop where
  certified : F.BlockCertified input
structure FiniteState (F : Framework) (input : Input F)
    {scope : ScopedState F input} {compatible : CompatibleState F input scope}
    (_block : BlockState F input compatible) : Prop where finite : F.FiniteRange input
structure RepeatedState (F : Framework) (input : Input F)
    {scope : ScopedState F input} {compatible : CompatibleState F input scope}
    (_block : BlockState F input compatible) : Prop where repeated : F.RepeatedIncrements input
structure C5Certificate (F : Framework) (input : Input F)
    {scope : ScopedState F input} {compatible : CompatibleState F input scope}
    {block : BlockState F input compatible} (_finite : FiniteState F input block) : Prop where
  exhausted : F.NoFiniteSurvivors input
  closes : F.entry.C5Claim input.G input.branch
structure C1Certificate (F : Framework) (input : Input F)
    {scope : ScopedState F input} {compatible : CompatibleState F input scope}
    {block : BlockState F input compatible} (_repeated : RepeatedState F input block) : Prop where
  forced : F.ArithmeticForcesTarget input
  closes : F.entry.C1Claim input.G input.branch
structure CT3Payload (F : Framework) (input : Input F)
    {scope : ScopedState F input} (_incompatible : IncompatibleState F input scope) where
  downstream : CT3.Input F.ct3
  aligned : F.CT3Aligned input downstream
structure CT10Payload (F : Framework) (input : Input F)
    {scope : ScopedState F input} (_incompatible : IncompatibleState F input scope) where
  downstream : CT10.Interface.Input F.ct10
  aligned : F.CT10Aligned input downstream
structure CT8Payload (F : Framework) (input : Input F)
    {scope : ScopedState F input} {compatible : CompatibleState F input scope}
    {block : BlockState F input compatible} (_finite : FiniteState F input block) where
  downstream : CT8.Interface.Input F.ct8
  aligned : F.CT8Aligned input downstream
structure CT14Payload (F : Framework) (input : Input F)
    {scope : ScopedState F input} {compatible : CompatibleState F input scope}
    {block : BlockState F input compatible} (_repeated : RepeatedState F input block) where
  downstream : CT14.Interface.Input F.ct14
  aligned : F.CT14Aligned input downstream
namespace CT3Payload
def toInput {F : Framework} {input : Input F} {scope : ScopedState F input}
    {state : IncompatibleState F input scope} (p : CT3Payload F input state) : CT3.Input F.ct3 := p.downstream
end CT3Payload
namespace CT10Payload
def toInput {F : Framework} {input : Input F} {scope : ScopedState F input}
    {state : IncompatibleState F input scope} (p : CT10Payload F input state) :
    CT10.Interface.Input F.ct10 := p.downstream
end CT10Payload
namespace CT8Payload
def toInput {F : Framework} {input : Input F} {scope : ScopedState F input}
    {compatible : CompatibleState F input scope} {block : BlockState F input compatible}
    {finite : FiniteState F input block} (p : CT8Payload F input finite) :
    CT8.Interface.Input F.ct8 := p.downstream
end CT8Payload
namespace CT14Payload
def toInput {F : Framework} {input : Input F} {scope : ScopedState F input}
    {compatible : CompatibleState F input scope} {block : BlockState F input compatible}
    {repeated : RepeatedState F input block} (p : CT14Payload F input repeated) :
    CT14.Interface.Input F.ct14 := p.downstream
end CT14Payload
inductive HandoffPayload (F : Framework) (input : Input F) where
  | ct3 {scope : ScopedState F input} {state : IncompatibleState F input scope}
      (payload : CT3Payload F input state)
  | ct10 {scope : ScopedState F input} {state : IncompatibleState F input scope}
      (payload : CT10Payload F input state)
  | ct8 {scope : ScopedState F input} {compatible : CompatibleState F input scope}
      {block : BlockState F input compatible} {finite : FiniteState F input block}
      (payload : CT8Payload F input finite)
  | ct14 {scope : ScopedState F input} {compatible : CompatibleState F input scope}
      {block : BlockState F input compatible} {repeated : RepeatedState F input block}
      (payload : CT14Payload F input repeated)
structure Port (F : Framework) (input : Input F) where accepts : HandoffPayload F input → Prop
structure HandoffPlan (F : Framework) (input : Input F) (port : Port F input) where
  accept : ∀ payload : HandoffPayload F input, port.accepts payload

end StructuralExhaustion.CT17
