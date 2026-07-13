import StructuralExhaustion.CT1.Automation
import StructuralExhaustion.CT2.Automation
import StructuralExhaustion.CT2.LocalDeletion

namespace StructuralExhaustion.Routes.CT1ToCT2

universe uAmbient uBranch uIndex uWitness
universe uPiece uInterface uAbstract uContext uCandidate

/-- Stable audit contract for the framework-generated CT1→CT2 route. -/
def contract : Core.RouteContract where
  routeId := "CT1.residual.avoiding->CT2"
  sourceResidualKind := "CT1.residual.avoiding"
  targetTacticId := "CT2"
  discovery := "StructuralExhaustion.CT2.Capability.discover"
  triggerConstructor := "StructuralExhaustion.Routes.CT1ToCT2.buildTrigger"
  soundnessTheorem := "StructuralExhaustion.Routes.CT1ToCT2.enabled_sound"
  contextPreservationTheorem :=
    "StructuralExhaustion.Routes.CT1ToCT2.branchContext_preserved"
  provenanceTheorem :=
    "StructuralExhaustion.Routes.CT1ToCT2.generated_route_id"
  selectionClass := .priority
  semanticDiscovery := .capabilityDiscovery
  problemSpecificInputs := [.targetCapability, .minimalityKernel]

/-- Existentially package the predecessor equivalence index of CT1's sole
semantic residual.  The inherited branch remains a dependent index. -/
structure PackedAvoiding
    {P : Core.Problem.{uAmbient, uBranch}}
    (S : CT1.Spec.{uIndex, uWitness} P) (input : CT1.Input P) : Type where
  equivalence : CT1.EquivalenceState S input
  state : CT1.AvoidingState S input equivalence

namespace PackedAvoiding

/-- Extract CT1's semantic residual from a result already known to have
reached the avoiding terminal. -/
def ofResult
    {P : Core.Problem.{uAmbient, uBranch}}
    {S : CT1.Spec.{uIndex, uWitness} P} {input : CT1.Input P}
    (result : CT1.ExecutionResult S input)
    (terminal : result.terminal = .avoiding) : PackedAvoiding S input := by
  cases result with
  | mk terminalId path outcome =>
      cases outcome with
      | c1 certificate => cases terminal
      | avoiding state => exact ⟨_, state⟩

end PackedAvoiding

/-- Extend the CT1 residual by the one shared minimality theorem.  The branch
context itself is inherited definitionally through `toAvoidingContext`. -/
def targetContext
    {P : Core.Problem.{uAmbient, uBranch}}
    {S : CT1.Spec.{uIndex, uWitness} P} {input : CT1.Input P}
    (minimality : Core.MinimalityKernel P (CT1.Target S) input.context)
    (source : PackedAvoiding S input) :
    Core.MinimalCounterexampleContext P (CT1.Target S) :=
  Core.MinimalCounterexampleContext.ofAvoiding
    source.state.toAvoidingContext minimality

/-- The unique framework route CT1→CT2.  Discovery is CT2's generic
capability search.  Its discovered value already has the exact target trigger
type, so trigger construction is the identity and its context is enforced by
Lean. -/
def rule
    {P : Core.Problem.{uAmbient, uBranch}}
    {S : CT1.Spec.{uIndex, uWitness} P} {input : CT1.Input P}
    (capability : CT2.Capability.{uAmbient, uBranch, uPiece, uInterface,
      uAbstract, uContext, uCandidate} P (CT1.Target S))
    (minimality : Core.MinimalityKernel P (CT1.Target S) input.context) :
    Core.Routing.RouteRule
      (PackedAvoiding S input) capability.tacticInterface where
  routeId := "CT1.residual.avoiding->CT2"
  targetContext := targetContext minimality
  Seed := fun source => CT2.Input capability (targetContext minimality source)
  discover := fun source => capability.discover (targetContext minimality source)
  buildTrigger := fun _source trigger => trigger

/-- Public trigger constructor.  Its dependent result has the exact target
context, so no separate admission theorem is needed. -/
def buildTrigger
    {P : Core.Problem.{uAmbient, uBranch}}
    {S : CT1.Spec.{uIndex, uWitness} P} {input : CT1.Input P}
    (capability : CT2.Capability.{uAmbient, uBranch, uPiece, uInterface,
      uAbstract, uContext, uCandidate} P (CT1.Target S))
    (minimality : Core.MinimalityKernel P (CT1.Target S) input.context)
    (source : PackedAvoiding S input)
    (seed : (rule capability minimality).Seed source) :
    CT2.Input capability (targetContext minimality source) :=
  (rule capability minimality).buildTrigger source seed

/-- The complete inherited branch context is preserved definitionally. -/
theorem branchContext_preserved
    {P : Core.Problem.{uAmbient, uBranch}}
    {S : CT1.Spec.{uIndex, uWitness} P} {input : CT1.Input P}
    (minimality : Core.MinimalityKernel P (CT1.Target S) input.context)
    (source : PackedAvoiding S input) :
    (targetContext minimality source).toBranchContext = input.context :=
  rfl

theorem ambient_preserved
    {P : Core.Problem.{uAmbient, uBranch}}
    {S : CT1.Spec.{uIndex, uWitness} P} {input : CT1.Input P}
    (minimality : Core.MinimalityKernel P (CT1.Target S) input.context)
    (source : PackedAvoiding S input) :
    (targetContext minimality source).G = input.context.G :=
  rfl

theorem state_preserved
    {P : Core.Problem.{uAmbient, uBranch}}
    {S : CT1.Spec.{uIndex, uWitness} P} {input : CT1.Input P}
    (minimality : Core.MinimalityKernel P (CT1.Target S) input.context)
    (source : PackedAvoiding S input) :
    (targetContext minimality source).state = input.context.state :=
  rfl

theorem baseline_preserved
    {P : Core.Problem.{uAmbient, uBranch}}
    {S : CT1.Spec.{uIndex, uWitness} P} {input : CT1.Input P}
    (minimality : Core.MinimalityKernel P (CT1.Target S) input.context)
    (source : PackedAvoiding S input) :
    (targetContext minimality source).baseline = input.context.baseline :=
  rfl

theorem avoidance_preserved
    {P : Core.Problem.{uAmbient, uBranch}}
    {S : CT1.Spec.{uIndex, uWitness} P} {input : CT1.Input P}
    (minimality : Core.MinimalityKernel P (CT1.Target S) input.context)
    (source : PackedAvoiding S input) :
    (targetContext minimality source).avoids = source.state.targetAvoiding :=
  rfl

/-- Every enabled route contains the exact proper/admissible seed certified by
CT2 discovery. -/
theorem enabled_sound
    {P : Core.Problem.{uAmbient, uBranch}}
    {S : CT1.Spec.{uIndex, uWitness} P} {input : CT1.Input P}
    {capability : CT2.Capability.{uAmbient, uBranch, uPiece, uInterface,
      uAbstract, uContext, uCandidate} P (CT1.Target S)}
    {minimality : Core.MinimalityKernel P (CT1.Target S) input.context}
    {source : PackedAvoiding S input}
    {trigger : (rule capability minimality).Seed source}
    (_enabled :
      (rule capability minimality).discover source = .enabled trigger) :
    capability.pieces.Proper trigger.seed.piece ∧
      capability.pieces.Admissible
        (targetContext minimality source).state trigger.seed.piece :=
  ⟨trigger.seed.proper, trigger.seed.admissible⟩

/-- Disabled discovery is an exact mathematical absence result, not a scope
tag: every enumerated piece fails properness or admissibility. -/
theorem disabled_sound
    {P : Core.Problem.{uAmbient, uBranch}}
    {S : CT1.Spec.{uIndex, uWitness} P} {input : CT1.Input P}
    {capability : CT2.Capability.{uAmbient, uBranch, uPiece, uInterface,
      uAbstract, uContext, uCandidate} P (CT1.Target S)}
    {minimality : Core.MinimalityKernel P (CT1.Target S) input.context}
    {source : PackedAvoiding S input}
    {reject : (rule capability minimality).Seed source → False}
    (_disabled :
      (rule capability minimality).discover source = .disabled reject) :
    ∀ piece : capability.pieces.Piece (targetContext minimality source).G,
      ¬ capability.pieces.Proper piece ∨
        ¬ capability.pieces.Admissible
          (targetContext minimality source).state piece := by
  intro piece
  cases properDecision : capability.pieces.properDecidable piece with
  | isFalse notProper => exact Or.inl notProper
  | isTrue proper =>
      cases admissibleDecision : capability.pieces.admissibleDecidable
          (targetContext minimality source).state piece with
      | isFalse notAdmissible => exact Or.inr notAdmissible
      | isTrue admissible =>
          exact (reject ⟨⟨piece, proper, admissible⟩⟩).elim

/-- Stable route provenance is fixed by the framework rule. -/
theorem generated_route_id
    {P : Core.Problem.{uAmbient, uBranch}}
    {S : CT1.Spec.{uIndex, uWitness} P} {input : CT1.Input P}
    (capability : CT2.Capability.{uAmbient, uBranch, uPiece, uInterface,
      uAbstract, uContext, uCandidate} P (CT1.Target S))
    (minimality : Core.MinimalityKernel P (CT1.Target S) input.context)
    (source : PackedAvoiding S input)
    (seed : (rule capability minimality).Seed source) :
    ((rule capability minimality).generate source seed).routeId =
      "CT1.residual.avoiding->CT2" :=
  rfl

end StructuralExhaustion.Routes.CT1ToCT2

namespace StructuralExhaustion.Routes.CT1ToCT2.LocalDeletion

universe uAmbient uBranch uIndex uWitness uPiece

open StructuralExhaustion.Routes.CT1ToCT2

/-!
# CT1 avoidance to local-deletion CT2

This route is the target-decision-free profile of CT1-to-CT2.  It preserves
the CT1 branch through the shared minimality kernel and searches only the
consumer's declared local piece enumeration.
-/

/-- Route a CT1 avoiding residual to the local deletion CT2 interface. -/
def rule
    {P : Core.Problem.{uAmbient, uBranch}}
    {S : CT1.Spec.{uIndex, uWitness} P} {input : CT1.Input P}
    (capability : CT2.LocalDeletionCapability.{uAmbient, uBranch, uPiece} P)
    (minimality : Core.MinimalityKernel P (CT1.Target S) input.context) :
    Core.Routing.RouteRule
      (PackedAvoiding S input)
      (capability.tacticInterface (CT1.Target S)) where
  routeId := "CT1.residual.avoiding->CT2.localDeletion"
  targetContext := CT1ToCT2.targetContext minimality
  Seed := fun source => CT2.LocalDeletionInput capability
    (CT1ToCT2.targetContext minimality source)
  discover := fun source => capability.discover
    (CT1ToCT2.targetContext minimality source)
  buildTrigger := fun _source trigger => trigger

/-- Construct the exact local-deletion trigger selected by discovery. -/
def buildTrigger
    {P : Core.Problem.{uAmbient, uBranch}}
    {S : CT1.Spec.{uIndex, uWitness} P} {input : CT1.Input P}
    (capability : CT2.LocalDeletionCapability.{uAmbient, uBranch, uPiece} P)
    (minimality : Core.MinimalityKernel P (CT1.Target S) input.context)
    (source : PackedAvoiding S input)
    (seed : (rule capability minimality).Seed source) :
    CT2.LocalDeletionInput capability
      (CT1ToCT2.targetContext minimality source) :=
  (rule capability minimality).buildTrigger source seed

/-- The complete inherited branch context is definitionally preserved. -/
theorem branchContext_preserved
    {P : Core.Problem.{uAmbient, uBranch}}
    {S : CT1.Spec.{uIndex, uWitness} P} {input : CT1.Input P}
    (minimality : Core.MinimalityKernel P (CT1.Target S) input.context)
    (source : PackedAvoiding S input) :
    (CT1ToCT2.targetContext minimality source).toBranchContext =
      input.context :=
  CT1ToCT2.branchContext_preserved minimality source

theorem ambient_preserved
    {P : Core.Problem.{uAmbient, uBranch}}
    {S : CT1.Spec.{uIndex, uWitness} P} {input : CT1.Input P}
    (minimality : Core.MinimalityKernel P (CT1.Target S) input.context)
    (source : PackedAvoiding S input) :
    (CT1ToCT2.targetContext minimality source).G = input.context.G :=
  CT1ToCT2.ambient_preserved minimality source

theorem state_preserved
    {P : Core.Problem.{uAmbient, uBranch}}
    {S : CT1.Spec.{uIndex, uWitness} P} {input : CT1.Input P}
    (minimality : Core.MinimalityKernel P (CT1.Target S) input.context)
    (source : PackedAvoiding S input) :
    (CT1ToCT2.targetContext minimality source).state = input.context.state :=
  CT1ToCT2.state_preserved minimality source

theorem baseline_preserved
    {P : Core.Problem.{uAmbient, uBranch}}
    {S : CT1.Spec.{uIndex, uWitness} P} {input : CT1.Input P}
    (minimality : Core.MinimalityKernel P (CT1.Target S) input.context)
    (source : PackedAvoiding S input) :
    (CT1ToCT2.targetContext minimality source).baseline =
      input.context.baseline :=
  CT1ToCT2.baseline_preserved minimality source

theorem avoidance_preserved
    {P : Core.Problem.{uAmbient, uBranch}}
    {S : CT1.Spec.{uIndex, uWitness} P} {input : CT1.Input P}
    (minimality : Core.MinimalityKernel P (CT1.Target S) input.context)
    (source : PackedAvoiding S input) :
    (CT1ToCT2.targetContext minimality source).avoids =
      source.state.targetAvoiding :=
  CT1ToCT2.avoidance_preserved minimality source

/-- Enabled discovery returns exactly one proper admissible local piece. -/
theorem enabled_sound
    {P : Core.Problem.{uAmbient, uBranch}}
    {S : CT1.Spec.{uIndex, uWitness} P} {input : CT1.Input P}
    {capability : CT2.LocalDeletionCapability.{uAmbient, uBranch, uPiece} P}
    {minimality : Core.MinimalityKernel P (CT1.Target S) input.context}
    {source : PackedAvoiding S input}
    {trigger : (rule capability minimality).Seed source}
    (_enabled : (rule capability minimality).discover source =
      .enabled trigger) :
    capability.pieces.Proper trigger.seed.piece ∧
      capability.pieces.Admissible
        (CT1ToCT2.targetContext minimality source).state trigger.seed.piece :=
  ⟨trigger.seed.proper, trigger.seed.admissible⟩

/-- Disabled discovery proves that every declared piece fails properness or
admissibility. -/
theorem disabled_sound
    {P : Core.Problem.{uAmbient, uBranch}}
    {S : CT1.Spec.{uIndex, uWitness} P} {input : CT1.Input P}
    {capability : CT2.LocalDeletionCapability.{uAmbient, uBranch, uPiece} P}
    {minimality : Core.MinimalityKernel P (CT1.Target S) input.context}
    {source : PackedAvoiding S input}
    {reject : (rule capability minimality).Seed source → False}
    (_disabled : (rule capability minimality).discover source =
      .disabled reject) :
    ∀ piece : capability.pieces.Piece
        (CT1ToCT2.targetContext minimality source).G,
      ¬ capability.pieces.Proper piece ∨
        ¬ capability.pieces.Admissible
          (CT1ToCT2.targetContext minimality source).state piece := by
  intro piece
  cases capability.pieces.properDecidable piece with
  | isFalse notProper => exact Or.inl notProper
  | isTrue proper =>
      cases capability.pieces.admissibleDecidable
          (CT1ToCT2.targetContext minimality source).state piece with
      | isFalse notAdmissible => exact Or.inr notAdmissible
      | isTrue admissible =>
          exact (reject ⟨⟨piece, proper, admissible⟩⟩).elim

/-- A valid local deletion closure forces route discovery to be disabled:
an enabled trigger executes the deletion-C2 path and contradicts minimality. -/
theorem discover_disabled_of_closure
    {P : Core.Problem.{uAmbient, uBranch}}
    {S : CT1.Spec.{uIndex, uWitness} P} {input : CT1.Input P}
    {capability : CT2.LocalDeletionCapability.{uAmbient, uBranch, uPiece} P}
    (minimality : Core.MinimalityKernel P (CT1.Target S) input.context)
    (source : PackedAvoiding S input)
    (closure : CT2.LocalDeletionClosureRule (Target := CT1.Target S)
      capability) :
    ∃ reject, (rule capability minimality).discover source =
      .disabled reject := by
  cases discovery : (rule capability minimality).discover source with
  | enabled trigger =>
      exact (closure.run (CT1ToCT2.targetContext minimality source)
        (buildTrigger capability minimality source trigger)).verified.elim
  | disabled reject => exact ⟨reject, rfl⟩

/-- Stable provenance of every enabled generated route. -/
theorem generated_route_id
    {P : Core.Problem.{uAmbient, uBranch}}
    {S : CT1.Spec.{uIndex, uWitness} P} {input : CT1.Input P}
    (capability : CT2.LocalDeletionCapability.{uAmbient, uBranch, uPiece} P)
    (minimality : Core.MinimalityKernel P (CT1.Target S) input.context)
    (source : PackedAvoiding S input)
    (seed : (rule capability minimality).Seed source) :
    ((rule capability minimality).generate source seed).routeId =
      "CT1.residual.avoiding->CT2.localDeletion" :=
  rfl

/-- Machine-readable contract for the target-decision-free CT1-to-CT2 route. -/
def contract : Core.RouteContract where
  routeId := "CT1.residual.avoiding->CT2.localDeletion"
  sourceResidualKind := "CT1.residual.avoiding"
  targetTacticId := "CT2"
  discovery :=
    "StructuralExhaustion.CT2.LocalDeletionCapability.discover"
  triggerConstructor :=
    "StructuralExhaustion.Routes.CT1ToCT2.LocalDeletion.buildTrigger"
  soundnessTheorem :=
    "StructuralExhaustion.Routes.CT1ToCT2.LocalDeletion.enabled_sound"
  contextPreservationTheorem :=
    "StructuralExhaustion.Routes.CT1ToCT2.LocalDeletion.branchContext_preserved"
  provenanceTheorem :=
    "StructuralExhaustion.Routes.CT1ToCT2.LocalDeletion.generated_route_id"
  selectionClass := .priority
  semanticDiscovery := .capabilityDiscovery
  problemSpecificInputs := [.targetCapability, .minimalityKernel]

end StructuralExhaustion.Routes.CT1ToCT2.LocalDeletion
