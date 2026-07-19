import StructuralExhaustion.CT7.Automation
import StructuralExhaustion.CT9.Automation
import StructuralExhaustion.Routes.CT9ToCT7

namespace StructuralExhaustion.Examples.CT9ToCT7AutomationFirst

open StructuralExhaustion

def problem : Core.Problem where
  Ambient := Unit
  Baseline := fun _ => True
  rank := fun _ => 0
  BranchState := fun _ => Unit

def context : Core.BranchContext problem := ⟨(), trivial, ()⟩

def items : Core.OrderedCollection Nat where
  values := [0, 1]
  nodup := by decide
  decEq := inferInstance

def sourceCapability : CT9.Capability problem where
  Item := Nat
  Label := Unit
  labels := Core.Enumeration.unit
  label := fun _item => ()
  capacity := fun _label => 1

def sourceInput : CT9.Input sourceCapability := ⟨context, items⟩

def source : CT9.OverloadResidual sourceCapability sourceInput :=
  CT9.runOverloadResidualOfTotalCapacityLtCardinality
    sourceCapability sourceInput (by decide)

def targetSpec : CT7.Spec problem where
  Object := Nat
  Context := Bool
  Realizes := fun _ctx _object _test => False
  response := fun _ctx object test => (object % 2 == 0) == test

def targetCapability : CT7.Capability targetSpec where
  contexts := fun _ctx _left _right => Core.Enumeration.bool
  realizesDecidable := fun _ctx _object _test => isFalse id

def adapter : Routes.CT9ToCT7.ObjectAdapter Nat Nat := ⟨id⟩

abbrev routedTransition := Routes.CT9ToCT7.transition
  (sourceCapability := sourceCapability) (sourceInput := sourceInput)
  targetCapability adapter (fun _label => rfl)

abbrev sourceStage : Core.Routing.ResidualStage .ct9
    (CT9.OverloadResidual sourceCapability sourceInput) :=
  Core.Routing.ResidualStage.exact source

abbrev routedExecution := routedTransition.onLedger id

def routedStage : routedExecution.EnabledStage sourceStage :=
  Routes.CT9ToCT7.advance targetCapability adapter
    (fun _label => rfl) id sourceStage

def routedLedger := routedStage.ledgerStage

def routedInput : CT7.Input targetSpec context :=
  routedTransition.trigger sourceStage ()

def targetResult := routedStage.targetResult

theorem route_id :
    routedTransition.profileId = "CT9.residual.overload->CT7" :=
  Routes.CT9ToCT7.transition_profile_id _ _ _

theorem route_context : routedTransition.targetContext sourceStage = context :=
  rfl

theorem source_distinct :
    (Routes.CT9ToCT7.sourcePair source rfl).first ≠
      (Routes.CT9ToCT7.sourcePair source rfl).second :=
  Routes.CT9ToCT7.source_pair_distinct source rfl

theorem mapped_objects :
    routedInput.left =
        adapter.object (Routes.CT9ToCT7.sourcePair source rfl).first ∧
      routedInput.right =
        adapter.object (Routes.CT9ToCT7.sourcePair source rfl).second :=
  by
    exact ⟨rfl, rfl⟩

theorem target_terminal : targetResult.terminal = .distinguishing := by
  decide

theorem target_trace :
    targetResult.trace =
      [.entry, .realizationSearch, .distinctionSearch, .distinguishingTerminal] := by
  decide

theorem target_verified : targetResult.outcome.Valid :=
  CT7.run_verified targetSpec targetCapability context routedInput

theorem target_total :
    ∃ result : CT7.ExecutionResult targetSpec targetCapability context routedInput,
      result.outcome.Valid ∧
        CT7.Graph.ValidTrace targetSpec targetCapability context routedInput
          result.trace :=
  CT7.run_total targetSpec targetCapability context routedInput

end StructuralExhaustion.Examples.CT9ToCT7AutomationFirst
