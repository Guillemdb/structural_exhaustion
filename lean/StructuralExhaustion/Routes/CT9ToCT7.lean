import StructuralExhaustion.CT7.Capability
import StructuralExhaustion.CT9.Search

namespace StructuralExhaustion.Routes.CT9ToCT7

universe uResidual uItem uLabel uObject

/-!
# CT9 overload to CT7 response comparison

An overloaded capacity-one CT9 fibre contains two distinct same-label items.
This route maps those exact items to the two objects consumed by CT7 while
preserving the complete branch context.  The framework owns pair extraction,
trigger construction, and provenance; an application supplies only the
item-to-object interpretation.
-/

structure ObjectAdapter (Item : Type uItem) (Object : Type uObject) where
  object : Item → Object

namespace ObjectAdapter

/-- A total item interpretation makes the overload route constructively
enabled. The source residual already contains the exact overloaded pair, so
discovery has no remaining search obligation. -/
def discover {Item : Type uItem} {Object : Type uObject}
    {Residual : Type uResidual}
    (_adapter : ObjectAdapter Item Object) (_source : Residual) :
    Core.Routing.Discovery Unit :=
  .enabled ()

end ObjectAdapter

def targetContext
    {P : Core.Problem}
    {sourceCapability : CT9.Capability.{_, _, uItem, uLabel} P}
    {sourceInput : CT9.Input sourceCapability}
    (_source : CT9.OverloadResidual sourceCapability sourceInput) :
    Core.BranchContext P :=
  sourceInput.context

def sourcePair
    {P : Core.Problem}
    {sourceCapability : CT9.Capability.{_, _, uItem, uLabel} P}
    {sourceInput : CT9.Input sourceCapability}
    (source : CT9.OverloadResidual sourceCapability sourceInput)
    (capacityOne : sourceCapability.capacity source.label = 1) :
    CT9.SameLabelPair sourceCapability sourceInput source.label :=
  source.sameLabelPairOfCapacityOne capacityOne

def rule
    {P : Core.Problem}
    {sourceCapability : CT9.Capability.{_, _, uItem, uLabel} P}
    {sourceInput : CT9.Input sourceCapability}
    {targetSpec : CT7.Spec P}
    (targetCapability : CT7.Capability targetSpec)
    (adapter : ObjectAdapter sourceCapability.Item targetSpec.Object)
    (capacityOne : ∀ label, sourceCapability.capacity label = 1) :
    Core.Routing.RouteRule
      (CT9.OverloadResidual sourceCapability sourceInput)
      targetCapability.tacticInterface where
  routeId := "CT9.residual.overload->CT7"
  targetContext := targetContext
  Seed := fun _source => Unit
  discover := ObjectAdapter.discover adapter
  buildTrigger := fun source _seed =>
    let pair := sourcePair source (capacityOne source.label)
    ⟨adapter.object pair.first, adapter.object pair.second⟩

def buildInput
    {P : Core.Problem}
    {sourceCapability : CT9.Capability.{_, _, uItem, uLabel} P}
    {sourceInput : CT9.Input sourceCapability}
    {targetSpec : CT7.Spec P}
    (targetCapability : CT7.Capability targetSpec)
    (adapter : ObjectAdapter sourceCapability.Item targetSpec.Object)
    (capacityOne : ∀ label, sourceCapability.capacity label = 1)
    (source : CT9.OverloadResidual sourceCapability sourceInput) :
    CT7.Input targetSpec (targetContext source) :=
  (rule targetCapability adapter capacityOne).buildTrigger source ()

theorem branchContext_preserved
    {P : Core.Problem}
    {sourceCapability : CT9.Capability.{_, _, uItem, uLabel} P}
    {sourceInput : CT9.Input sourceCapability}
    (source : CT9.OverloadResidual sourceCapability sourceInput) :
    targetContext source = sourceInput.context :=
  rfl

theorem input_objects_are_mapped_pair
    {P : Core.Problem}
    {sourceCapability : CT9.Capability.{_, _, uItem, uLabel} P}
    {sourceInput : CT9.Input sourceCapability}
    {targetSpec : CT7.Spec P}
    (targetCapability : CT7.Capability targetSpec)
    (adapter : ObjectAdapter sourceCapability.Item targetSpec.Object)
    (capacityOne : ∀ label, sourceCapability.capacity label = 1)
    (source : CT9.OverloadResidual sourceCapability sourceInput) :
    let pair := sourcePair source (capacityOne source.label)
    (buildInput targetCapability adapter capacityOne source).left =
        adapter.object pair.first ∧
      (buildInput targetCapability adapter capacityOne source).right =
        adapter.object pair.second :=
  ⟨rfl, rfl⟩

theorem source_pair_distinct
    {P : Core.Problem}
    {sourceCapability : CT9.Capability.{_, _, uItem, uLabel} P}
    {sourceInput : CT9.Input sourceCapability}
    (source : CT9.OverloadResidual sourceCapability sourceInput)
    (capacityOne : sourceCapability.capacity source.label = 1) :
    (sourcePair source capacityOne).first ≠
      (sourcePair source capacityOne).second :=
  (sourcePair source capacityOne).distinct

theorem enabled_generates
    {P : Core.Problem}
    {sourceCapability : CT9.Capability.{_, _, uItem, uLabel} P}
    {sourceInput : CT9.Input sourceCapability}
    {targetSpec : CT7.Spec P}
    (targetCapability : CT7.Capability targetSpec)
    (adapter : ObjectAdapter sourceCapability.Item targetSpec.Object)
    (capacityOne : ∀ label, sourceCapability.capacity label = 1)
    (source : CT9.OverloadResidual sourceCapability sourceInput) :
    ((rule targetCapability adapter capacityOne).attempt source).generated? =
      some ((rule targetCapability adapter capacityOne).generate source ()) :=
  rfl

theorem generated_route_id
    {P : Core.Problem}
    {sourceCapability : CT9.Capability.{_, _, uItem, uLabel} P}
    {sourceInput : CT9.Input sourceCapability}
    {targetSpec : CT7.Spec P}
    (targetCapability : CT7.Capability targetSpec)
    (adapter : ObjectAdapter sourceCapability.Item targetSpec.Object)
    (capacityOne : ∀ label, sourceCapability.capacity label = 1)
    (source : CT9.OverloadResidual sourceCapability sourceInput) :
    ((rule targetCapability adapter capacityOne).generate source ()).routeId =
      "CT9.residual.overload->CT7" :=
  rfl

def routeContract : Core.RouteContract where
  routeId := "CT9.residual.overload->CT7"
  sourceResidualKind := "CT9.residual.overload"
  targetTacticId := "CT7"
  discovery := "StructuralExhaustion.Routes.CT9ToCT7.ObjectAdapter.discover"
  triggerConstructor := "StructuralExhaustion.Routes.CT9ToCT7.buildInput"
  soundnessTheorem := "StructuralExhaustion.Routes.CT9ToCT7.enabled_generates"
  contextPreservationTheorem :=
    "StructuralExhaustion.Routes.CT9ToCT7.branchContext_preserved"
  provenanceTheorem :=
    "StructuralExhaustion.Routes.CT9ToCT7.generated_route_id"
  selectionClass := .forced
  semanticDiscovery := .problemSemanticAdapter
    "StructuralExhaustion.Routes.CT9ToCT7.ObjectAdapter"
  problemSpecificInputs := [.targetCapability, .semanticDiscoveryAdapter]

end StructuralExhaustion.Routes.CT9ToCT7
