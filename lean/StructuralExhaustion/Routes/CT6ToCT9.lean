import StructuralExhaustion.CT6.State
import StructuralExhaustion.CT9.Capability

namespace StructuralExhaustion.Routes.CT6ToCT9

universe uResidual uItem
universe uAmbient uBranch uIndex uData uLabel

/-!
Canonical typed routing from a CT6 active-ledger residual to CT9.

CT6 proves that every monitored failure is absent and retains the inherited
branch context.  The only cross-tactic semantic choice is which declared finite
collection CT9 should partition.  A problem instance supplies that collection
through `ItemCollectionAdapter`; the framework owns discovery, context and
trigger construction, input materialization, and route provenance.
-/

/-- Problem-specific interpretation of a predecessor residual as CT9's
declared item collection.  Duplicate-freedom and decidable equality are part
of `Core.OrderedCollection`; any stronger semantic meaning of the items remains
an application theorem. -/
structure ItemCollectionAdapter (Residual : Type uResidual)
    (Item : Type uItem) where
  items : Residual → Core.OrderedCollection Item

namespace ItemCollectionAdapter

/-- Ignore residual payload fields when the target collection is already
fixed by the inherited branch state.  This is the canonical adapter for a
constant exact collection; applications need not repeat a one-field lambda. -/
def constant {Residual : Type uResidual} {Item : Type uItem}
    (items : Core.OrderedCollection Item) :
    ItemCollectionAdapter Residual Item where
  items := fun _source => items

@[simp] theorem constant_items
    {Residual : Type uResidual} {Item : Type uItem}
    (items : Core.OrderedCollection Item) (source : Residual) :
    (constant (Residual := Residual) items).items source = items :=
  rfl

/-- A total item adapter makes the CT6→CT9 route constructively enabled.
Discovery is framework-owned; the problem author supplies only `items`. -/
def discover {Residual : Type uResidual} {Item : Type uItem}
    (_adapter : ItemCollectionAdapter Residual Item)
    (_source : Residual) : Core.Routing.Discovery Unit :=
  .enabled ()

end ItemCollectionAdapter

/-- CT6 and CT9 share the complete branch context definitionally. -/
def targetContext
    {P : Core.Problem.{uAmbient, uBranch}}
    {S : CT6.Spec.{uIndex, uData} P}
    {sourceCapability : CT6.Capability S}
    {input : CT6.Input P}
    (_source : CT6.ActiveLedgerResidual S sourceCapability input) :
    Core.BranchContext P :=
  input

/-- Framework route rule.  `Unit` is the seed because a total item adapter
has no further invocation-specific discovery obligation. -/
def rule
    {P : Core.Problem.{uAmbient, uBranch}}
    {S : CT6.Spec.{uIndex, uData} P}
    {sourceCapability : CT6.Capability S}
    {input : CT6.Input P}
    (targetCapability : CT9.Capability.{uAmbient, uBranch, uItem, uLabel} P)
    (adapter : ItemCollectionAdapter
      (CT6.ActiveLedgerResidual S sourceCapability input)
      targetCapability.Item) :
    Core.Routing.RouteRule
      (CT6.ActiveLedgerResidual S sourceCapability input)
      (CT9.tacticInterface targetCapability) where
  routeId := "CT6.residual.activeLedger->CT9"
  targetContext := targetContext
  Seed := fun _source => Unit
  discover := adapter.discover
  buildTrigger := fun source _seed => ⟨adapter.items source⟩

/-- Public trigger constructor.  Its dependent result fixes the exact branch
context inherited from CT6. -/
def buildTrigger
    {P : Core.Problem.{uAmbient, uBranch}}
    {S : CT6.Spec.{uIndex, uData} P}
    {sourceCapability : CT6.Capability S}
    {input : CT6.Input P}
    (targetCapability : CT9.Capability.{uAmbient, uBranch, uItem, uLabel} P)
    (adapter : ItemCollectionAdapter
      (CT6.ActiveLedgerResidual S sourceCapability input)
      targetCapability.Item)
    (source : CT6.ActiveLedgerResidual S sourceCapability input) :
    CT9.Trigger targetCapability (targetContext source) :=
  (rule targetCapability adapter).buildTrigger source ()

/-- Materialize the ordinary CT9 runner input from the generated trigger. -/
def buildInput
    {P : Core.Problem.{uAmbient, uBranch}}
    {S : CT6.Spec.{uIndex, uData} P}
    {sourceCapability : CT6.Capability S}
    {input : CT6.Input P}
    (targetCapability : CT9.Capability.{uAmbient, uBranch, uItem, uLabel} P)
    (adapter : ItemCollectionAdapter
      (CT6.ActiveLedgerResidual S sourceCapability input)
      targetCapability.Item)
    (source : CT6.ActiveLedgerResidual S sourceCapability input) :
    CT9.Input targetCapability :=
  CT9.Input.ofTrigger (targetContext source)
    (buildTrigger targetCapability adapter source)

theorem branchContext_preserved
    {P : Core.Problem.{uAmbient, uBranch}}
    {S : CT6.Spec.{uIndex, uData} P}
    {sourceCapability : CT6.Capability S}
    {input : CT6.Input P}
    (source : CT6.ActiveLedgerResidual S sourceCapability input) :
    targetContext source = input :=
  rfl

theorem ambient_preserved
    {P : Core.Problem.{uAmbient, uBranch}}
    {S : CT6.Spec.{uIndex, uData} P}
    {sourceCapability : CT6.Capability S}
    {input : CT6.Input P}
    (source : CT6.ActiveLedgerResidual S sourceCapability input) :
    (targetContext source).G = input.G :=
  rfl

theorem baseline_preserved
    {P : Core.Problem.{uAmbient, uBranch}}
    {S : CT6.Spec.{uIndex, uData} P}
    {sourceCapability : CT6.Capability S}
    {input : CT6.Input P}
    (source : CT6.ActiveLedgerResidual S sourceCapability input) :
    (targetContext source).baseline = input.baseline :=
  rfl

theorem state_preserved
    {P : Core.Problem.{uAmbient, uBranch}}
    {S : CT6.Spec.{uIndex, uData} P}
    {sourceCapability : CT6.Capability S}
    {input : CT6.Input P}
    (source : CT6.ActiveLedgerResidual S sourceCapability input) :
    (targetContext source).state = input.state :=
  rfl

theorem input_context_preserved
    {P : Core.Problem.{uAmbient, uBranch}}
    {S : CT6.Spec.{uIndex, uData} P}
    {sourceCapability : CT6.Capability S}
    {input : CT6.Input P}
    (targetCapability : CT9.Capability.{uAmbient, uBranch, uItem, uLabel} P)
    (adapter : ItemCollectionAdapter
      (CT6.ActiveLedgerResidual S sourceCapability input)
      targetCapability.Item)
    (source : CT6.ActiveLedgerResidual S sourceCapability input) :
    (buildInput targetCapability adapter source).context = input :=
  rfl

theorem input_items_are_adapted
    {P : Core.Problem.{uAmbient, uBranch}}
    {S : CT6.Spec.{uIndex, uData} P}
    {sourceCapability : CT6.Capability S}
    {input : CT6.Input P}
    (targetCapability : CT9.Capability.{uAmbient, uBranch, uItem, uLabel} P)
    (adapter : ItemCollectionAdapter
      (CT6.ActiveLedgerResidual S sourceCapability input)
      targetCapability.Item)
    (source : CT6.ActiveLedgerResidual S sourceCapability input) :
    (buildInput targetCapability adapter source).items = adapter.items source :=
  rfl

/-- The predecessor's exhaustive activity theorem remains available after
input materialization; routing does not weaken or reconstruct it. -/
theorem active_evidence_preserved
    {P : Core.Problem.{uAmbient, uBranch}}
    {S : CT6.Spec.{uIndex, uData} P}
    {sourceCapability : CT6.Capability S}
    {input : CT6.Input P}
    (source : CT6.ActiveLedgerResidual S sourceCapability input) :
    ∀ index, ¬ S.Failure input index :=
  source.noFailure

/-- The total adapter always produces the unique enabled route attempt. -/
theorem enabled_generates
    {P : Core.Problem.{uAmbient, uBranch}}
    {S : CT6.Spec.{uIndex, uData} P}
    {sourceCapability : CT6.Capability S}
    {input : CT6.Input P}
    (targetCapability : CT9.Capability.{uAmbient, uBranch, uItem, uLabel} P)
    (adapter : ItemCollectionAdapter
      (CT6.ActiveLedgerResidual S sourceCapability input)
      targetCapability.Item)
    (source : CT6.ActiveLedgerResidual S sourceCapability input) :
    ((rule targetCapability adapter).attempt source).generated? =
      some ((rule targetCapability adapter).generate source ()) := by
  rfl

theorem generated_route_id
    {P : Core.Problem.{uAmbient, uBranch}}
    {S : CT6.Spec.{uIndex, uData} P}
    {sourceCapability : CT6.Capability S}
    {input : CT6.Input P}
    (targetCapability : CT9.Capability.{uAmbient, uBranch, uItem, uLabel} P)
    (adapter : ItemCollectionAdapter
      (CT6.ActiveLedgerResidual S sourceCapability input)
      targetCapability.Item)
    (source : CT6.ActiveLedgerResidual S sourceCapability input) :
    ((rule targetCapability adapter).generate source ()).routeId =
      "CT6.residual.activeLedger->CT9" :=
  rfl

/-- Machine-readable authoring boundary for the framework-owned route. -/
def routeContract : Core.RouteContract where
  routeId := "CT6.residual.activeLedger->CT9"
  sourceResidualKind := "CT6.residual.activeLedger"
  targetTacticId := "CT9"
  discovery :=
    "StructuralExhaustion.Routes.CT6ToCT9.ItemCollectionAdapter.discover"
  triggerConstructor := "StructuralExhaustion.Routes.CT6ToCT9.buildTrigger"
  soundnessTheorem := "StructuralExhaustion.Routes.CT6ToCT9.enabled_generates"
  contextPreservationTheorem :=
    "StructuralExhaustion.Routes.CT6ToCT9.branchContext_preserved"
  provenanceTheorem :=
    "StructuralExhaustion.Routes.CT6ToCT9.generated_route_id"
  selectionClass := .forced
  semanticDiscovery := .problemSemanticAdapter
    "StructuralExhaustion.Routes.CT6ToCT9.ItemCollectionAdapter"
  problemSpecificInputs := [.targetCapability, .semanticDiscoveryAdapter]

end StructuralExhaustion.Routes.CT6ToCT9
