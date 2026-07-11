import StructuralExhaustion.CT7.Interface
import StructuralExhaustion.CT8.Interface
import StructuralExhaustion.CT12.Interface

namespace StructuralExhaustion.CT3

universe uA uB uP uI uC uT u7 u12 u8

/-!
Proof-carrying vocabulary for CT3.

The framework contains only stable mathematical operations.  Runtime control
flow is expressed by the indexed states below, so a node can be implemented
and verified using only its immediate input and output contracts.
-/

/-- Mathematical vocabulary required by external-type compression. -/
structure Framework where
  Ambient : Type uA
  BranchState : Ambient → Type uB
  Piece : Type uP
  Interface : Type uI
  Context : Type uC
  ExternalType : Type uT

  interface : Piece → Interface
  externalType : Piece → ExternalType
  CertifiedInterface : Piece → Prop
  TypeIndexFinite : Interface → Prop
  Compatible : Interface → Context → Prop
  Response : Piece → Context → Prop
  TypeAccepts : ExternalType → Context → Prop
  TypeIncluded : ExternalType → ExternalType → Prop

  ReplacementAdmissible :
    (G : Ambient) → BranchState G → Piece → Piece → Prop
  SmallerReplacement :
    (G : Ambient) → BranchState G → Piece → Piece → Prop
  ReplacementPreserves :
    (G : Ambient) → BranchState G → Piece → Piece → Prop
  TypeDataPersists :
    (G : Ambient) → BranchState G → Piece → Prop

  C2Claim : (G : Ambient) → BranchState G → Prop
  C3Claim : (G : Ambient) → BranchState G → Prop
  C5Claim : (G : Ambient) → BranchState G → Prop

  ct7 : CT7.Interface.Framework.{u7, u7, u7, u7, u7, u7}
  ct8 : CT8.Interface.Framework.{u8, u8, u8, u8, u8}
  ct12 : CT12.Interface.Framework.{u12, u12, u12, u12}
  CT7Aligned :
    (G : Ambient) → BranchState G → Piece → CT7.Interface.Input ct7 → Prop
  CT8Aligned :
    (G : Ambient) → BranchState G → Piece → CT8.Interface.Input ct8 → Prop
  CT12Aligned :
    (G : Ambient) → BranchState G → Piece → CT12.Interface.Input ct12 → Prop

/-- Validated CT3 invocation.  Finiteness and semantic equivalence are
established by later nodes. -/
structure Input (F : Framework) where
  G : F.Ambient
  branch : F.BranchState G
  X : F.Piece
  certifiedInterface : F.CertifiedInterface X

def TypeIndexFiniteAt (F : Framework) (input : Input F) : Prop :=
  F.TypeIndexFinite (F.interface input.X)

structure ScopeCandidate (F : Framework) (input : Input F) : Prop where
  infiniteIndex : ¬ TypeIndexFiniteAt F input

structure ScopedState (F : Framework) (input : Input F) : Prop where
  finiteIndex : TypeIndexFiniteAt F input

/-- S-Equiv certificate: the stored external type decides every compatible
response before replacement comparison begins. -/
structure EquivalenceCertificate (F : Framework) (input : Input F) : Prop where
  decidesResponses :
    ∀ context : F.Context,
      F.Compatible (F.interface input.X) context →
      (F.Response input.X context ↔
        F.TypeAccepts (F.externalType input.X) context)

structure EquivalenceState (F : Framework) (input : Input F) : Prop where
  scope : ScopedState F input
  certificate : EquivalenceCertificate F input

/-- A single admissible smaller representative with every proof required for
the C2 terminal. -/
structure ReplacementWitness (F : Framework) (input : Input F) where
  replacement : F.Piece
  admissible :
    F.ReplacementAdmissible input.G input.branch input.X replacement
  smaller :
    F.SmallerReplacement input.G input.branch input.X replacement
  included :
    F.TypeIncluded
      (F.externalType replacement) (F.externalType input.X)
  preserves :
    F.ReplacementPreserves input.G input.branch input.X replacement
  closes : F.C2Claim input.G input.branch

structure C2Certificate (F : Framework) (input : Input F)
    (_equivalence : EquivalenceState F input) where
  witness : ReplacementWitness F input

/-- Exhaustive failure of compression, indexed by the equivalence state used
for the search. -/
structure UncompressibleState (F : Framework) (input : Input F)
    (_equivalence : EquivalenceState F input) : Prop where
  noReplacement : ReplacementWitness F input → False

structure C3Certificate (F : Framework) (input : Input F)
    {equivalence : EquivalenceState F input}
    (_state : UncompressibleState F input equivalence) where
  closes : F.C3Claim input.G input.branch

structure CT7Payload (F : Framework) (input : Input F)
    {equivalence : EquivalenceState F input}
    (_state : UncompressibleState F input equivalence) where
  downstream : CT7.Interface.Input F.ct7
  aligned : F.CT7Aligned input.G input.branch input.X downstream

structure CT12Payload (F : Framework) (input : Input F)
    {equivalence : EquivalenceState F input}
    (_state : UncompressibleState F input equivalence) where
  downstream : CT12.Interface.Input F.ct12
  aligned : F.CT12Aligned input.G input.branch input.X downstream

/-- S-Pers is a certification boundary.  Missing persistence is a design-time
obligation and cannot become a runtime tag. -/
structure PersistentState (F : Framework) (input : Input F)
    {equivalence : EquivalenceState F input}
    (_state : UncompressibleState F input equivalence) : Prop where
  persists : F.TypeDataPersists input.G input.branch input.X

structure C5Certificate (F : Framework) (input : Input F)
    {equivalence : EquivalenceState F input}
    {state : UncompressibleState F input equivalence}
    (_persistent : PersistentState F input state) where
  closes : F.C5Claim input.G input.branch

structure CT8Payload (F : Framework) (input : Input F)
    {equivalence : EquivalenceState F input}
    {state : UncompressibleState F input equivalence}
    (_persistent : PersistentState F input state) where
  downstream : CT8.Interface.Input F.ct8
  aligned : F.CT8Aligned input.G input.branch input.X downstream

namespace CT7Payload
def toInput {F : Framework} {input : Input F}
    {equivalence : EquivalenceState F input}
    {state : UncompressibleState F input equivalence}
    (payload : CT7Payload F input state) : CT7.Interface.Input F.ct7 :=
  payload.downstream
end CT7Payload

namespace CT8Payload
def toInput {F : Framework} {input : Input F}
    {equivalence : EquivalenceState F input}
    {state : UncompressibleState F input equivalence}
    {persistent : PersistentState F input state}
    (payload : CT8Payload F input persistent) : CT8.Interface.Input F.ct8 :=
  payload.downstream
end CT8Payload

namespace CT12Payload
def toInput {F : Framework} {input : Input F}
    {equivalence : EquivalenceState F input}
    {state : UncompressibleState F input equivalence}
    (payload : CT12Payload F input state) : CT12.Interface.Input F.ct12 :=
  payload.downstream
end CT12Payload

inductive HandoffPayload (F : Framework) (input : Input F) where
  | ct7 {equivalence : EquivalenceState F input}
      {state : UncompressibleState F input equivalence}
      (payload : CT7Payload F input state)
  | ct12 {equivalence : EquivalenceState F input}
      {state : UncompressibleState F input equivalence}
      (payload : CT12Payload F input state)
  | ct8 {equivalence : EquivalenceState F input}
      {state : UncompressibleState F input equivalence}
      {persistent : PersistentState F input state}
      (payload : CT8Payload F input persistent)

structure Port (F : Framework) (input : Input F) where
  accepts : HandoffPayload F input → Prop

structure HandoffPlan (F : Framework) (input : Input F)
    (port : Port F input) where
  accept : ∀ payload : HandoffPayload F input, port.accepts payload

end StructuralExhaustion.CT3
