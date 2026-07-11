import StructuralExhaustion.CT4.Types
import StructuralExhaustion.CT12.Interface
import StructuralExhaustion.CT13.Interface

namespace StructuralExhaustion.CT12

/-! Proof-carrying vocabulary for CT12's well-founded peeling loop. -/

structure Framework where
  entry : Interface.Framework
  ct4 : CT4.Framework
  ct13 : CT13.Interface.Framework
  LoopInvariant : Interface.Input entry → Nat → Prop
  PeelCertified : Interface.Input entry → Nat → Prop
  StateRestored : Interface.Input entry → Nat → Nat → Prop
  CT4Aligned : Interface.Input entry → CT4.Input ct4 → Prop
  CT13Aligned : Interface.Input entry → CT13.Interface.Input ct13 → Prop

abbrev Input (F : Framework) := Interface.Input F.entry
def ScopeReadyAt (F : Framework) (input : Input F) : Prop := Interface.ScopeReadyAt F.entry input
structure ScopeCandidate (F : Framework) (input : Input F) : Prop where
  unavailable : ¬ ScopeReadyAt F input
structure ScopedState (F : Framework) (input : Input F) : Prop where ready : ScopeReadyAt F input

/-- The loop state is indexed by the current recorded load. -/
structure LoopState (F : Framework) (input : Input F) (load : Nat) : Prop where
  invariant : F.LoopInvariant input load

structure PeelableState (F : Framework) (input : Input F) {load : Nat}
    (_state : LoopState F input load) : Prop where
  positive : 0 < load

structure PeeledState (F : Framework) (input : Input F) {load : Nat}
    {state : LoopState F input load} (_peelable : PeelableState F input state) : Prop where
  certified : F.PeelCertified input load

/-- S-Rest is carried independently of S-Meas. -/
structure RestoredState (F : Framework) (input : Input F) {load : Nat}
    {state : LoopState F input load} {peelable : PeelableState F input state}
    (_peeled : PeeledState F input peelable) (next : Nat) : Prop where
  nextState : LoopState F input next
  restored : F.StateRestored input load next

/-- The sole license for the back edge. -/
structure DecreasedState (F : Framework) (input : Input F) {load : Nat}
    {state : LoopState F input load} {peelable : PeelableState F input state}
    {peeled : PeeledState F input peelable} {next : Nat}
    (restored : RestoredState F input peeled next) : Prop where
  decreases : next < load

namespace DecreasedState
def loopState {F : Framework} {input : Input F} {load : Nat}
    {state : LoopState F input load} {peelable : PeelableState F input state}
    {peeled : PeeledState F input peelable} {next : Nat}
    {restored : RestoredState F input peeled next}
    (_decreased : DecreasedState F input restored) : LoopState F input next :=
  restored.nextState
end DecreasedState

structure C4Certificate (F : Framework) (input : Input F) {load : Nat}
    (_state : LoopState F input load) : Prop where
  closes : F.entry.C4Claim input.G input.branch

structure CT4Payload (F : Framework) (input : Input F) {load : Nat}
    {state : LoopState F input load} {peelable : PeelableState F input state}
    (_peeled : PeeledState F input peelable) where
  downstream : CT4.Input F.ct4
  aligned : F.CT4Aligned input downstream

structure CT13Payload (F : Framework) (input : Input F) {load : Nat}
    {state : LoopState F input load} {peelable : PeelableState F input state}
    (_peeled : PeeledState F input peelable) where
  downstream : CT13.Interface.Input F.ct13
  aligned : F.CT13Aligned input downstream

namespace CT4Payload
def toInput {F : Framework} {input : Input F} {load : Nat}
    {state : LoopState F input load} {peelable : PeelableState F input state}
    {peeled : PeeledState F input peelable} (p : CT4Payload F input peeled) :
    CT4.Input F.ct4 := p.downstream
end CT4Payload
namespace CT13Payload
def toInput {F : Framework} {input : Input F} {load : Nat}
    {state : LoopState F input load} {peelable : PeelableState F input state}
    {peeled : PeeledState F input peelable} (p : CT13Payload F input peeled) :
    CT13.Interface.Input F.ct13 := p.downstream
end CT13Payload

inductive HandoffPayload (F : Framework) (input : Input F) where
  | ct4 {load : Nat} {state : LoopState F input load}
      {peelable : PeelableState F input state} {peeled : PeeledState F input peelable}
      (payload : CT4Payload F input peeled)
  | ct13 {load : Nat} {state : LoopState F input load}
      {peelable : PeelableState F input state} {peeled : PeeledState F input peelable}
      (payload : CT13Payload F input peeled)
structure Port (F : Framework) (input : Input F) where accepts : HandoffPayload F input → Prop
structure HandoffPlan (F : Framework) (input : Input F) (port : Port F input) where
  accept : ∀ payload : HandoffPayload F input, port.accepts payload

end StructuralExhaustion.CT12
