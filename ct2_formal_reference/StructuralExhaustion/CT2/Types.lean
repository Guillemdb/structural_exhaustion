import StructuralExhaustion.CT3.Types
import StructuralExhaustion.CT10.Interface

namespace StructuralExhaustion.CT2

universe uA uP uI uO uR uC uM
universe u3A u3B u3P u3I u3C u3T u37 u312 u38
universe u10A u10B u10R u10D u10L u10T

/-!
The semantic vocabulary and proof-carrying states used by the CT2 machine.

The control-flow graph and interpreter deliberately live in later modules.  In
particular, none of the mathematical contracts below depends on a diagram node
number or on a downstream consumer.
-/

/-- Mathematical operations and predicates required by CT2. -/
structure Framework where
  Ambient : Type uA
  Piece : Type uP
  Interface : Type uI
  Outside : Type uO
  Rank : Type uR

  rank : Ambient → Rank
  smaller : Rank → Rank → Prop

  Baseline : Ambient → Prop
  Target : Ambient → Prop

  Proper : Ambient → Piece → Prop
  Admissible : Ambient → Piece → Prop
  interface : Piece → Interface
  InterfaceBounded : Interface → Prop

  Compatible : Interface → Outside → Prop
  Response : Piece → Outside → Prop

  delete : Ambient → Piece → Ambient
  replace : Ambient → Piece → Piece → Ambient
  ReplacementAllowed : Ambient → Piece → Piece → Prop

  CriticalityDatum : Ambient → Piece → Type uC
  MissingResponseDatum : Ambient → Piece → Type uM

  /-- Exact consumer framework for both CT3 exits. -/
  ct3 : CT3.Framework.{u3A, u3B, u3P, u3I, u3C, u3T, u37, u312, u38}
  ct10 : CT10.Interface.Framework.{u10A, u10B, u10R, u10D, u10L, u10T}
  ContextCT3Aligned :
    Ambient → Piece → Piece → Outside → CT3.Input ct3 → Prop
  ResponseCT3Aligned :
    (G : Ambient) → (X : Piece) →
    MissingResponseDatum G X → CT3.Input ct3 → Prop
  CriticalityCT10Aligned :
    (G : Ambient) → (X : Piece) →
    CriticalityDatum G X → CT10.Interface.Input ct10 → Prop

/-- A counterexample satisfies the baseline assumptions and avoids the target. -/
def Counterexample (F : Framework) (G : F.Ambient) : Prop :=
  F.Baseline G ∧ ¬ F.Target G

/-- The exact minimality eliminator consumed by CT2.

Well-foundedness belongs to the upstream construction of a minimal object; the
CT2 engine itself needs only this local elimination principle. -/
structure MinimalCounterexample (F : Framework) (G : F.Ambient) : Prop where
  counterexample : Counterexample F G
  excludesSmaller :
    ∀ H : F.Ambient,
      F.smaller (F.rank H) (F.rank G) →
      ¬ Counterexample F H

/-- Validated CT2 entry data. -/
structure Input (F : Framework) where
  G : F.Ambient
  X : F.Piece
  minimal : MinimalCounterexample F G
  proper : F.Proper G X
  admissible : F.Admissible G X

def InterfaceBoundedAt (F : Framework) (input : Input F) : Prop :=
  F.InterfaceBounded (F.interface input.X)

/-- A typed scope exit: CT2 cannot admit this interface. -/
structure ScopeCandidate (F : Framework) (input : Input F) : Prop where
  unbounded : ¬ InterfaceBoundedAt F input

/-- State after the interface admission node. -/
structure BoundedState (F : Framework) (input : Input F) : Prop where
  bounded : InterfaceBoundedAt F input

/-- A deletion that is a strict smaller counterexample. -/
structure DeletionWitness (F : Framework) (input : Input F) : Prop where
  smaller :
    F.smaller
      (F.rank (F.delete input.G input.X))
      (F.rank input.G)
  baseline : F.Baseline (F.delete input.G input.X)
  targetAvoiding : ¬ F.Target (F.delete input.G input.X)

namespace DeletionWitness

def counterexample {F : Framework} {input : Input F}
    (witness : DeletionWitness F input) :
    Counterexample F (F.delete input.G input.X) :=
  ⟨witness.baseline, witness.targetAvoiding⟩

end DeletionWitness

/-- State produced by a negative deletion decision. -/
structure DeletionCriticalState (F : Framework) (input : Input F) : Prop where
  bounded : BoundedState F input
  critical : ¬ DeletionWitness F input

/-- The response profile used to compare a piece with a replacement. -/
def TargetResponseProfile (F : Framework) (X : F.Piece)
    (outside : F.Outside) : Prop :=
  F.Compatible (F.interface X) outside ∧ F.Response X outside

/-- A smaller replacement candidate.  This record contains only the local
candidate conditions; context safety is certified by the following node. -/
structure SmallerReplacementCandidate (F : Framework) (input : Input F) where
  replacement : F.Piece
  allowed : F.ReplacementAllowed input.G input.X replacement
  sameInterface : F.interface replacement = F.interface input.X
  profileIncluded :
    ∀ outside : F.Outside,
      TargetResponseProfile F replacement outside →
      TargetResponseProfile F input.X outside
  smaller :
    F.smaller
      (F.rank (F.replace input.G input.X replacement))
      (F.rank input.G)

/-- State after the candidate-search node chooses a concrete smaller candidate. -/
structure CandidateState (F : Framework) (input : Input F) where
  deletionCritical : DeletionCriticalState F input
  candidate : SmallerReplacementCandidate F input

/-- Candidate-specific context certification.  Unlike a family-wide context
predicate, this proposition talks only about the candidate that
the machine actually selected. -/
structure CandidateContextCertificate
    (F : Framework) (input : Input F)
    (state : CandidateState F input) : Prop where
  profilePreserved :
    ∀ outside : F.Outside,
      TargetResponseProfile F input.X outside →
      TargetResponseProfile F state.candidate.replacement outside
  replacementCounterexample :
    Counterexample F
      (F.replace input.G input.X state.candidate.replacement)

/-- A useful, explicit failure of candidate-specific context certification.

The outside context witnesses a response supported by the original piece but
missing from the candidate.  Counterexample preservation is a separate C2
prerequisite and therefore belongs only to the certified branch. -/
structure ContextResidual
    (F : Framework) (input : Input F)
    (state : CandidateState F input) where
  outside : F.Outside
  compatible : F.Compatible (F.interface input.X) outside
  sourceResponds : F.Response input.X outside
  replacementMissingResponse :
    ¬ F.Response state.candidate.replacement outside

namespace ContextResidual

theorem notProfilePreserved {F : Framework} {input : Input F}
    {state : CandidateState F input}
    (residual : ContextResidual F input state) :
    ¬ (∀ outside : F.Outside,
      TargetResponseProfile F input.X outside →
      TargetResponseProfile F state.candidate.replacement outside) := by
  intro preserved
  have sourceProfile : TargetResponseProfile F input.X residual.outside :=
    ⟨residual.compatible, residual.sourceResponds⟩
  have replacementProfile := preserved residual.outside sourceProfile
  exact residual.replacementMissingResponse replacementProfile.2

end ContextResidual

/-- Exhaustion proof returned when no smaller candidate exists. -/
abbrev TargetUncompressible (F : Framework) (input : Input F) : Prop :=
  SmallerReplacementCandidate F input → False

/-- Complete state passed to the final survivor classifier. -/
structure SurvivorState (F : Framework) (input : Input F) : Prop where
  deletionCritical : DeletionCriticalState F input
  targetUncompressible : TargetUncompressible F input

/-- Context-dependent CT3 payload, indexed by the exact candidate state and
carrying an aligned validated consumer input. -/
structure ContextCT3Payload (F : Framework) (input : Input F)
    (state : CandidateState F input) where
  residual : ContextResidual F input state
  downstream : CT3.Input F.ct3
  aligned :
    F.ContextCT3Aligned input.G input.X state.candidate.replacement
      residual.outside downstream

/-- Criticality-refinement raw CT10 payload.  It retains the complete survivor
state instead of discarding the facts that justified the route. -/
structure CriticalityCT10Payload (F : Framework) (input : Input F)
    (_survivor : SurvivorState F input) where
  datum : F.CriticalityDatum input.G input.X
  downstream : CT10.Interface.Input F.ct10
  aligned : F.CriticalityCT10Aligned input.G input.X datum downstream

/-- Missing-response CT3 payload, including its survivor state and aligned
validated consumer input. -/
structure ResponseCT3Payload (F : Framework) (input : Input F)
    (_survivor : SurvivorState F input) where
  datum : F.MissingResponseDatum input.G input.X
  downstream : CT3.Input F.ct3
  aligned : F.ResponseCT3Aligned input.G input.X datum downstream

/-- The two semantically distinct CT3 inputs emitted by CT2. -/
inductive CT3Payload (F : Framework) (input : Input F) where
  | context {state : CandidateState F input}
      (payload : ContextCT3Payload F input state)
  | missingResponse {survivor : SurvivorState F input}
      (payload : ResponseCT3Payload F input survivor)

namespace CT3Payload

/-- Both semantically distinct CT3 exits expose the exact validated consumer
input selected by their indexed payload. -/
def toInput {F : Framework} {input : Input F} :
    CT3Payload F input → CT3.Input F.ct3
  | .context payload => payload.downstream
  | .missingResponse payload => payload.downstream

end CT3Payload

/-- The CT10 input emitted by CT2, existentially packaging its survivor index. -/
inductive CT10Payload (F : Framework) (input : Input F) where
  | criticality {survivor : SurvivorState F input}
      (payload : CriticalityCT10Payload F input survivor)

namespace CT10Payload

def toInput {F : Framework} {input : Input F} :
    CT10Payload F input → CT10.Interface.Input F.ct10
  | .criticality payload => payload.downstream

end CT10Payload

/-- Provenance-safe C2 certificate.  The origin cannot disagree with the
witness because it is encoded by the constructor. -/
inductive C2Certificate (F : Framework) (input : Input F) where
  | deletion (witness : DeletionWitness F input)
  | replacement
      (state : CandidateState F input)
      (certificate : CandidateContextCertificate F input state)

namespace C2Certificate

def ofDeletion {F : Framework} {input : Input F}
    (witness : DeletionWitness F input) : C2Certificate F input :=
  .deletion witness

def ofReplacement {F : Framework} {input : Input F}
    (state : CandidateState F input)
    (certificate : CandidateContextCertificate F input state) :
    C2Certificate F input :=
  .replacement state certificate

def smallerObject {F : Framework} {input : Input F} :
    C2Certificate F input → F.Ambient
  | .deletion _ => F.delete input.G input.X
  | .replacement state _ =>
      F.replace input.G input.X state.candidate.replacement

theorem contradiction {F : Framework} {input : Input F}
    (certificate : C2Certificate F input) : False := by
  cases certificate with
  | deletion witness =>
      exact input.minimal.excludesSmaller
        (F.delete input.G input.X)
        witness.smaller
        witness.counterexample
  | replacement state context =>
      exact input.minimal.excludesSmaller
        (F.replace input.G input.X state.candidate.replacement)
        state.candidate.smaller
        context.replacementCounterexample

theorem exhaustive {F : Framework} {input : Input F}
    (certificate : C2Certificate F input) :
    (∃ witness : DeletionWitness F input,
      certificate = .deletion witness) ∨
    (∃ (state : CandidateState F input)
        (context : CandidateContextCertificate F input state),
      certificate = .replacement state context) := by
  cases certificate with
  | deletion witness => exact Or.inl ⟨witness, rfl⟩
  | replacement state context => exact Or.inr ⟨state, context, rfl⟩

end C2Certificate

/-- Generic downstream acceptance predicates.  These are intentionally not
part of any core CT2 decision contract. -/
structure Port (F : Framework) (input : Input F) where
  ct3Accepts : CT3Payload F input → Prop
  ct10Accepts : CT10Payload F input → Prop

/-- Consumer-side proofs, separate from the core decision plan. -/
structure HandoffPlan (F : Framework) (input : Input F)
    (port : Port F input) where
  acceptCT3 : ∀ payload : CT3Payload F input, port.ct3Accepts payload
  acceptCT10 : ∀ payload : CT10Payload F input, port.ct10Accepts payload

end StructuralExhaustion.CT2
