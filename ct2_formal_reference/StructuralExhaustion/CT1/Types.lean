import StructuralExhaustion.CT2.Types
import StructuralExhaustion.CT5.Types
import StructuralExhaustion.CT6.Interface
import StructuralExhaustion.CT17.Interface

namespace StructuralExhaustion.CT1

universe uA uP uInterface uO uR uC uM
universe u2_3A u2_3B u2_3P u2_3I u2_3C u2_3T u2_37 u2_312 u2_38
universe u2_10A u2_10B u2_10R u2_10D u2_10L u2_10T
universe u4A u4B u4D u4P u4C u4L u49 u414 u413
universe u5S u5W u511 u514
universe u6A u6B u6M u6T u6O u6W
universe uB uI uW u17

/-!
The mathematical vocabulary and proof-carrying staged states of CT1.

CT1 is parameterized by the CT2 framework that receives its `P₁→₂`
terminal.  This makes target avoidance and the CT2 target definition
definitionally identical and prevents an adapter from changing the ambient
object between the two tactics.
-/

/-- Vocabulary required by CT1.  Every handoff uses the exact validated entry
contract of its consumer. -/
structure Framework where
  ct2 : CT2.Framework.{uA, uP, uInterface, uO, uR, uC, uM,
    u2_3A, u2_3B, u2_3P, u2_3I, u2_3C, u2_3T, u2_37, u2_312, u2_38,
    u2_10A, u2_10B, u2_10R, u2_10D, u2_10L, u2_10T}
  ct5 : CT5.Framework.{u4A, u4B, u4D, u4P, u4C, u4L, u49, u414, u413,
    u5S, u5W, u511, u514}
  ct6 : CT6.Interface.Framework.{u6A, u6B, u6M, u6T, u6O, u6W}
  ct17 : CT17.Interface.Framework.{u17, u17, u17, u17, u17, u17}

  BranchState : ct2.Ambient → Type uB
  TestIndex : Type uI
  Witness :
    (G : ct2.Ambient) → BranchState G → TestIndex → Type uW
  Realizes :
    (G : ct2.Ambient) →
    (branch : BranchState G) →
    (index : TestIndex) →
    Witness G branch index → Prop

  ScopeReady : (G : ct2.Ambient) → BranchState G → Prop

  CT3Aligned :
    (G : ct2.Ambient) → BranchState G → CT3.Input ct2.ct3 → Prop
  CT4Aligned :
    (G : ct2.Ambient) → BranchState G → CT4.Input ct5.ct4 → Prop
  CT5Aligned :
    (G : ct2.Ambient) → BranchState G → CT5.Input ct5 → Prop
  CT6Aligned :
    (G : ct2.Ambient) → BranchState G → CT6.Interface.Input ct6 → Prop
  CT17Aligned :
    (G : ct2.Ambient) → BranchState G → CT17.Interface.Input ct17 → Prop

/-- Validated CT1 invocation.  Target-test equivalence and scope readiness are
produced by later nodes rather than assumed at entry. -/
structure Input (F : Framework) where
  G : F.ct2.Ambient
  branch : F.BranchState G
  baseline : F.ct2.Baseline G

/-- A concrete realized member of the supplied local-test family. -/
structure TestRealization (F : Framework) (input : Input F) where
  index : F.TestIndex
  witness : F.Witness input.G input.branch index
  realizes : F.Realizes input.G input.branch index witness

def ScopeReadyAt (F : Framework) (input : Input F) : Prop :=
  F.ScopeReady input.G input.branch

/-- Typed CT1 scope exit. -/
structure ScopeCandidate (F : Framework) (input : Input F) : Prop where
  unavailable : ¬ ScopeReadyAt F input

/-- State admitted by the scope node. -/
structure ScopedState (F : Framework) (input : Input F) : Prop where
  ready : ScopeReadyAt F input

/-- Exact equivalence between the target and realization of a supplied test.
The two directions remain separate fields because they have different proof
roles in applications. -/
structure EquivalenceCertificate
    (F : Framework) (input : Input F) : Prop where
  targetOfRealization :
    TestRealization F input → F.ct2.Target input.G
  realizationOfTarget :
    F.ct2.Target input.G → Nonempty (TestRealization F input)

/-- Complete predecessor state for the realization decision. -/
structure EquivalenceState
    (F : Framework) (input : Input F) : Prop where
  scope : ScopedState F input
  certificate : EquivalenceCertificate F input

/-- Negative realization state.  It stores both absence of every declared
test and the target-avoidance consequence used by every routed payload. -/
structure AvoidingState
    (F : Framework) (input : Input F) : Prop where
  equivalence : EquivalenceState F input
  noRealization : TestRealization F input → False
  targetAvoiding : ¬ F.ct2.Target input.G

namespace AvoidingState

def ofNoRealization {F : Framework} {input : Input F}
    (equivalence : EquivalenceState F input)
    (noRealization : TestRealization F input → False) :
    AvoidingState F input :=
  {
    equivalence := equivalence
    noRealization := noRealization
    targetAvoiding := by
      intro target
      exact equivalence.certificate.realizationOfTarget target |>.elim noRealization
  }

end AvoidingState

/-- Provenance-safe C1 certificate. -/
structure C1Certificate (F : Framework) (input : Input F) where
  equivalence : EquivalenceState F input
  realization : TestRealization F input

namespace C1Certificate

def target {F : Framework} {input : Input F}
    (certificate : C1Certificate F input) : F.ct2.Target input.G :=
  certificate.equivalence.certificate.targetOfRealization
    certificate.realization

end C1Certificate

/-- Exact `P₁→₂` payload.  The ambient object is fixed to `input.G`; target
avoidance is taken from the predecessor state; and the remaining fields are
precisely those required to construct `CT2.Input`. -/
structure CT2Payload (F : Framework) (input : Input F)
    (_avoiding : AvoidingState F input) where
  X : F.ct2.Piece
  excludesSmaller :
    ∀ H : F.ct2.Ambient,
      F.ct2.smaller (F.ct2.rank H) (F.ct2.rank input.G) →
      ¬ CT2.Counterexample F.ct2 H
  proper : F.ct2.Proper input.G X
  admissible : F.ct2.Admissible input.G X

namespace CT2Payload

def toInput {F : Framework} {input : Input F}
    {avoiding : AvoidingState F input}
    (payload : CT2Payload F input avoiding) : CT2.Input F.ct2 where
  G := input.G
  X := payload.X
  minimal := {
    counterexample := ⟨input.baseline, avoiding.targetAvoiding⟩
    excludesSmaller := payload.excludesSmaller
  }
  proper := payload.proper
  admissible := payload.admissible

end CT2Payload

/-- Exact `P₁→₃` input, indexed by the target-avoiding state and accompanied
by the application-specific alignment proof relating the two branch models. -/
structure CT3Payload (F : Framework) (input : Input F)
    (_avoiding : AvoidingState F input) where
  downstream : CT3.Input F.ct2.ct3
  aligned : F.CT3Aligned input.G input.branch downstream

/-- Exact `P₁→₄` input for the CT4 framework embedded by CT5. -/
structure CT4Payload (F : Framework) (input : Input F)
    (_avoiding : AvoidingState F input) where
  downstream : CT4.Input F.ct5.ct4
  aligned : F.CT4Aligned input.G input.branch downstream

/-- Exact `P₁→₅` input. -/
structure CT5Payload (F : Framework) (input : Input F)
    (_avoiding : AvoidingState F input) where
  downstream : CT5.Input F.ct5
  aligned : F.CT5Aligned input.G input.branch downstream

namespace CT3Payload

def toInput {F : Framework} {input : Input F}
    {avoiding : AvoidingState F input}
    (payload : CT3Payload F input avoiding) : CT3.Input F.ct2.ct3 :=
  payload.downstream

end CT3Payload

namespace CT4Payload

def toInput {F : Framework} {input : Input F}
    {avoiding : AvoidingState F input}
    (payload : CT4Payload F input avoiding) : CT4.Input F.ct5.ct4 :=
  payload.downstream

end CT4Payload

namespace CT5Payload

def toInput {F : Framework} {input : Input F}
    {avoiding : AvoidingState F input}
    (payload : CT5Payload F input avoiding) : CT5.Input F.ct5 :=
  payload.downstream

end CT5Payload

/-- Exact `P₁→₆` validated entry input. -/
structure CT6Payload (F : Framework) (input : Input F)
    (_avoiding : AvoidingState F input) where
  downstream : CT6.Interface.Input F.ct6
  aligned : F.CT6Aligned input.G input.branch downstream

namespace CT6Payload

def toInput {F : Framework} {input : Input F}
    {avoiding : AvoidingState F input}
    (payload : CT6Payload F input avoiding) : CT6.Interface.Input F.ct6 :=
  payload.downstream

end CT6Payload

/-- Exact `P₁→₁₇` validated entry input. -/
structure CT17Payload (F : Framework) (input : Input F)
    (_avoiding : AvoidingState F input) where
  downstream : CT17.Interface.Input F.ct17
  aligned : F.CT17Aligned input.G input.branch downstream

namespace CT17Payload
def toInput {F : Framework} {input : Input F} {avoiding : AvoidingState F input}
    (payload : CT17Payload F input avoiding) : CT17.Interface.Input F.ct17 :=
  payload.downstream
end CT17Payload

/-- Consumer-tagged handoff data.  The constructor fixes the consumer and
retains the target-avoiding predecessor index. -/
inductive HandoffPayload (F : Framework) (input : Input F) where
  | ct2 {avoiding : AvoidingState F input}
      (payload : CT2Payload F input avoiding)
  | ct3 {avoiding : AvoidingState F input}
      (payload : CT3Payload F input avoiding)
  | ct4 {avoiding : AvoidingState F input}
      (payload : CT4Payload F input avoiding)
  | ct5 {avoiding : AvoidingState F input}
      (payload : CT5Payload F input avoiding)
  | ct6 {avoiding : AvoidingState F input}
      (payload : CT6Payload F input avoiding)
  | ct17 {avoiding : AvoidingState F input}
      (payload : CT17Payload F input avoiding)

/-- Downstream acceptance is an adapter contract, not part of any CT1 node. -/
structure Port (F : Framework) (input : Input F) where
  accepts : HandoffPayload F input → Prop

/-- Consumer-side proofs for every typed handoff constructor. -/
structure HandoffPlan (F : Framework) (input : Input F)
    (port : Port F input) where
  accept : ∀ payload : HandoffPayload F input, port.accepts payload

end StructuralExhaustion.CT1
