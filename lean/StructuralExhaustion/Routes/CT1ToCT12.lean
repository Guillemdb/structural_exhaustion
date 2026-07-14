import StructuralExhaustion.CT1.State
import StructuralExhaustion.CT12.Capability

namespace StructuralExhaustion.Routes.CT1ToCT12

universe uAmbient uBranch uIndex uWitness
universe uState uPeeled uDemand uTier

/-!
# CT1 realization to CT12 peeling

This route preserves a successful CT1 certificate and the complete branch
context while materializing a CT12 loop state.  The relation between the
realized object and that loop state is necessarily problem-specific, so the
adapter must carry a proof of its declared `Evidence`; it cannot merely assert
that a transition is valid.
-/

/-- The semantic success retained at CT1's C1 terminal.  This is deliberately
proof-valued: routing may use the certified target theorem but cannot inspect
or enumerate its witness to manufacture downstream computational data. -/
abbrev PackedC1
    {P : Core.Problem.{uAmbient, uBranch}}
    (S : CT1.Spec.{uIndex, uWitness} P) (input : CT1.Input P) : Prop :=
  CT1.Target S input.context.G

namespace PackedC1

/-- Package one literal CT1 realization with the framework-certified target
equivalence. -/
def ofRealization
    {P : Core.Problem.{uAmbient, uBranch}}
    {S : CT1.Spec.{uIndex, uWitness} P} {input : CT1.Input P}
    (index : S.TestIndex) (witness : S.Witness input.context.G index)
    (realizes : S.Realizes input.context.G index witness) : PackedC1 S input :=
  ⟨index, witness, realizes⟩

theorem target
    {P : Core.Problem.{uAmbient, uBranch}}
    {S : CT1.Spec.{uIndex, uWitness} P} {input : CT1.Input P}
    (source : PackedC1 S input) : CT1.Target S input.context.G := source

end PackedC1

/-- Problem-semantic bridge from an exact CT1 success to a CT12 loop seed.
The adapter declares the evidence that makes the transition meaningful and
must prove it for every source certificate. -/
structure SemanticAdapter
    {P : Core.Problem.{uAmbient, uBranch}}
    {S : CT1.Spec.{uIndex, uWitness} P} {input : CT1.Input P}
    (targetCapability : CT12.Capability.{uAmbient, uBranch, uState,
      uPeeled, uDemand, uTier} P) where
  trigger : PackedC1 S input → CT12.Trigger targetCapability input.context
  Evidence : (source : PackedC1 S input) →
    CT12.Trigger targetCapability input.context → Prop
  evidence : (source : PackedC1 S input) → Evidence source (trigger source)

namespace SemanticAdapter

/-- A total, proof-carrying adapter makes the route constructively enabled. -/
def discover
    {P : Core.Problem.{uAmbient, uBranch}}
    {S : CT1.Spec.{uIndex, uWitness} P} {input : CT1.Input P}
    {targetCapability : CT12.Capability.{uAmbient, uBranch, uState,
      uPeeled, uDemand, uTier} P}
    (_adapter : SemanticAdapter (S := S) (input := input) targetCapability)
    (_source : PackedC1 S input) : Core.Routing.Discovery Unit :=
  .enabled ()

end SemanticAdapter

/-- Successful CT1 and CT12 share the whole branch context definitionally. -/
def targetContext
    {P : Core.Problem.{uAmbient, uBranch}}
    {S : CT1.Spec.{uIndex, uWitness} P} {input : CT1.Input P}
    (_source : PackedC1 S input) : Core.BranchContext P :=
  input.context

/-- Canonical framework route.  The semantic adapter is total, hence route
discovery has the unique `Unit` seed. -/
def rule
    {P : Core.Problem.{uAmbient, uBranch}}
    {S : CT1.Spec.{uIndex, uWitness} P} {input : CT1.Input P}
    (targetCapability : CT12.Capability.{uAmbient, uBranch, uState,
      uPeeled, uDemand, uTier} P)
    (adapter : SemanticAdapter (S := S) (input := input) targetCapability) :
    Core.Routing.RouteRule (PackedC1 S input)
      (CT12.tacticInterface targetCapability) where
  routeId := "CT1.terminal.c1->CT12"
  targetContext := targetContext
  Seed := fun _source => Unit
  discover := adapter.discover
  buildTrigger := fun source _seed => adapter.trigger source

def buildTrigger
    {P : Core.Problem.{uAmbient, uBranch}}
    {S : CT1.Spec.{uIndex, uWitness} P} {input : CT1.Input P}
    (targetCapability : CT12.Capability.{uAmbient, uBranch, uState,
      uPeeled, uDemand, uTier} P)
    (adapter : SemanticAdapter (S := S) (input := input) targetCapability)
    (source : PackedC1 S input) :
    CT12.Trigger targetCapability (targetContext source) :=
  (rule targetCapability adapter).buildTrigger source ()

/-- Materialize the ordinary CT12 runner input from the routed trigger. -/
def buildInput
    {P : Core.Problem.{uAmbient, uBranch}}
    {S : CT1.Spec.{uIndex, uWitness} P} {input : CT1.Input P}
    (targetCapability : CT12.Capability.{uAmbient, uBranch, uState,
      uPeeled, uDemand, uTier} P)
    (adapter : SemanticAdapter (S := S) (input := input) targetCapability)
    (source : PackedC1 S input) : CT12.Input targetCapability :=
  CT12.Input.ofTrigger (targetContext source)
    (buildTrigger targetCapability adapter source)

theorem branchContext_preserved
    {P : Core.Problem.{uAmbient, uBranch}}
    {S : CT1.Spec.{uIndex, uWitness} P} {input : CT1.Input P}
    (source : PackedC1 S input) : targetContext source = input.context := rfl

theorem input_context_preserved
    {P : Core.Problem.{uAmbient, uBranch}}
    {S : CT1.Spec.{uIndex, uWitness} P} {input : CT1.Input P}
    (targetCapability : CT12.Capability.{uAmbient, uBranch, uState,
      uPeeled, uDemand, uTier} P)
    (adapter : SemanticAdapter (S := S) (input := input) targetCapability)
    (source : PackedC1 S input) :
    (buildInput targetCapability adapter source).context = input.context := rfl

/-- The generated CT12 trigger retains the exact semantic bridge proved by
the adapter. -/
theorem evidence_preserved
    {P : Core.Problem.{uAmbient, uBranch}}
    {S : CT1.Spec.{uIndex, uWitness} P} {input : CT1.Input P}
    (targetCapability : CT12.Capability.{uAmbient, uBranch, uState,
      uPeeled, uDemand, uTier} P)
    (adapter : SemanticAdapter (S := S) (input := input) targetCapability)
    (source : PackedC1 S input) :
    adapter.Evidence source (buildTrigger targetCapability adapter source) :=
  by simpa [buildTrigger, rule] using adapter.evidence source

theorem enabled_generates
    {P : Core.Problem.{uAmbient, uBranch}}
    {S : CT1.Spec.{uIndex, uWitness} P} {input : CT1.Input P}
    (targetCapability : CT12.Capability.{uAmbient, uBranch, uState,
      uPeeled, uDemand, uTier} P)
    (adapter : SemanticAdapter (S := S) (input := input) targetCapability)
    (source : PackedC1 S input) :
    ((rule targetCapability adapter).attempt source).generated? =
      some ((rule targetCapability adapter).generate source ()) := rfl

theorem generated_route_id
    {P : Core.Problem.{uAmbient, uBranch}}
    {S : CT1.Spec.{uIndex, uWitness} P} {input : CT1.Input P}
    (targetCapability : CT12.Capability.{uAmbient, uBranch, uState,
      uPeeled, uDemand, uTier} P)
    (adapter : SemanticAdapter (S := S) (input := input) targetCapability)
    (source : PackedC1 S input) :
    ((rule targetCapability adapter).generate source ()).routeId =
      "CT1.terminal.c1->CT12" := rfl

/-- Machine-readable framework ownership record. -/
def routeContract : Core.RouteContract where
  routeId := "CT1.terminal.c1->CT12"
  sourceResidualKind := "CT1.terminal.c1"
  targetTacticId := "CT12"
  discovery :=
    "StructuralExhaustion.Routes.CT1ToCT12.SemanticAdapter.discover"
  triggerConstructor := "StructuralExhaustion.Routes.CT1ToCT12.buildTrigger"
  soundnessTheorem := "StructuralExhaustion.Routes.CT1ToCT12.evidence_preserved"
  contextPreservationTheorem :=
    "StructuralExhaustion.Routes.CT1ToCT12.branchContext_preserved"
  provenanceTheorem :=
    "StructuralExhaustion.Routes.CT1ToCT12.generated_route_id"
  selectionClass := .forced
  semanticDiscovery := .problemSemanticAdapter
    "StructuralExhaustion.Routes.CT1ToCT12.SemanticAdapter"
  problemSpecificInputs := [.targetCapability, .semanticDiscoveryAdapter]

end StructuralExhaustion.Routes.CT1ToCT12
