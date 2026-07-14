import StructuralExhaustion.CT14.Automation

namespace StructuralExhaustion.Routes.CT14ToCT14

open StructuralExhaustion

universe uSourceMember uSourceLabel uTargetMember uTargetLabel
universe uAmbient uBranch

/-!
# CT14 capacity-ledger refinement

One aggregate ledger can expose a bounded semantic family that is refined by
another CT14 capability on the identical branch.  Both member universes remain
independently declared by their capabilities; the route owns only forced
context preservation and the target's empty trigger.
-/

def targetContext
    {P : Core.Problem.{uAmbient, uBranch}}
    {sourceCapability : CT14.Capability.{uSourceMember, uSourceLabel} P}
    {ctx : Core.BranchContext P}
    (_source : CT14.CapacityResidual sourceCapability ctx) :
    Core.BranchContext P :=
  ctx

def rule
    {P : Core.Problem.{uAmbient, uBranch}}
    {sourceCapability : CT14.Capability.{uSourceMember, uSourceLabel} P}
    {ctx : Core.BranchContext P}
    (targetCapability : CT14.Capability.{uTargetMember, uTargetLabel} P) :
    Core.Routing.RouteRule (CT14.CapacityResidual sourceCapability ctx)
      targetCapability.tacticInterface where
  routeId := "CT14.residual.capacity->CT14"
  targetContext := targetContext
  Seed := fun _source => Unit
  discover := targetCapability.discover
  buildTrigger := fun _source _seed => ⟨⟩

def buildInput
    {P : Core.Problem.{uAmbient, uBranch}}
    {sourceCapability : CT14.Capability.{uSourceMember, uSourceLabel} P}
    {ctx : Core.BranchContext P}
    (targetCapability : CT14.Capability.{uTargetMember, uTargetLabel} P)
    (source : CT14.CapacityResidual sourceCapability ctx) :
    CT14.Input targetCapability (targetContext source) :=
  (rule targetCapability).buildTrigger source ()

theorem branchContext_preserved
    {P : Core.Problem.{uAmbient, uBranch}}
    {sourceCapability : CT14.Capability.{uSourceMember, uSourceLabel} P}
    {ctx : Core.BranchContext P}
    (source : CT14.CapacityResidual sourceCapability ctx) :
    targetContext source = ctx := rfl

theorem enabled_generates
    {P : Core.Problem.{uAmbient, uBranch}}
    {sourceCapability : CT14.Capability.{uSourceMember, uSourceLabel} P}
    {ctx : Core.BranchContext P}
    (targetCapability : CT14.Capability.{uTargetMember, uTargetLabel} P)
    (source : CT14.CapacityResidual sourceCapability ctx) :
    ((rule targetCapability).attempt source).generated? =
      some ((rule targetCapability).generate source ()) := rfl

theorem generated_route_id
    {P : Core.Problem.{uAmbient, uBranch}}
    {sourceCapability : CT14.Capability.{uSourceMember, uSourceLabel} P}
    {ctx : Core.BranchContext P}
    (targetCapability : CT14.Capability.{uTargetMember, uTargetLabel} P)
    (source : CT14.CapacityResidual sourceCapability ctx) :
    ((rule targetCapability).generate source ()).routeId =
      "CT14.residual.capacity->CT14" := rfl

def routeContract : Core.RouteContract where
  routeId := "CT14.residual.capacity->CT14"
  sourceResidualKind := "CT14.residual.capacity"
  targetTacticId := "CT14"
  discovery := "StructuralExhaustion.CT14.Capability.discover"
  triggerConstructor := "StructuralExhaustion.Routes.CT14ToCT14.buildInput"
  soundnessTheorem := "StructuralExhaustion.Routes.CT14ToCT14.enabled_generates"
  contextPreservationTheorem :=
    "StructuralExhaustion.Routes.CT14ToCT14.branchContext_preserved"
  provenanceTheorem :=
    "StructuralExhaustion.Routes.CT14ToCT14.generated_route_id"
  selectionClass := .forced
  semanticDiscovery := .capabilityDiscovery
  problemSpecificInputs := [.targetCapability]

end StructuralExhaustion.Routes.CT14ToCT14
