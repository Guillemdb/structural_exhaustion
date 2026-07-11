import StructuralExhaustion.CT13.Automation
import StructuralExhaustion.Examples.CT4Toy
import StructuralExhaustion.Examples.CT6CT10Interfaces

namespace StructuralExhaustion.Examples.CT13Toy
open StructuralExhaustion

def mkFramework (entry : CT13.Interface.Framework) : CT13.Framework where
  entry := entry
  ct4 := CT4Toy.framework
  ct9 := CT6CT10Fixtures.ct9Entry
  ct14 := CT6CT10Fixtures.ct14Entry
  TierOneAvailable := fun _ => True
  TierOneCanonical := fun _ => True
  MinimalObstruction := fun _ => True
  TierTwoCanonical := fun _ => True
  ResourcesReconciled := fun _ => True
  CombinedCapacity := fun _ => True
  CT4Aligned := fun _ _ => True
  CT9Aligned := fun _ _ => True
  CT14Aligned := fun _ _ => True
def framework := mkFramework CT6CT10Fixtures.ct13Entry
def input : CT13.Input framework := CT6CT10Fixtures.ct13Input

private def available (scope : CT13.ScopedState framework input) :
    CT13.AvailableState framework input scope := ⟨trivial⟩
private def impossibleReconciliation
    {scope : CT13.ScopedState framework input}
    {unavailable : CT13.UnavailableState framework input scope}
    (fallback : CT13.FallbackState framework input unavailable) :
    CT13.Nodes.Reconciliation.Contract framework input fallback :=
  False.elim (unavailable.unavailable trivial)
private def impossibleRouting
    {scope : CT13.ScopedState framework input}
    {unavailable : CT13.UnavailableState framework input scope}
    {fallback : CT13.FallbackState framework input unavailable}
    (overlap : CT13.OverlapState framework input fallback) :
    CT13.Nodes.Routing.Contract framework input overlap :=
  False.elim (unavailable.unavailable trivial)

def ct4Plan : CT13.CorePlan framework input where
  scope := { decide := .ready ⟨trivial⟩ }
  availability := { decide := fun scope => .available (available scope) }
  tierOne := { certify := fun _ => ⟨trivial⟩ }
  tierOneRouting := { route := fun _ => {
    downstream := CT4Toy.input, aligned := trivial } }
  fallback := { certify := fun unavailable => False.elim (unavailable.unavailable trivial) }
  reconciliation := { decide := impossibleReconciliation }
  comparison := { certify := fun _ => ⟨trivial, trivial⟩ }
  routing := { route := impossibleRouting }

def fallbackFramework : CT13.Framework :=
  { framework with TierOneAvailable := fun _ => False }
def fallbackInput : CT13.Input fallbackFramework := CT6CT10Fixtures.ct13Input
def c4Plan : CT13.CorePlan fallbackFramework fallbackInput where
  scope := { decide := .ready ⟨trivial⟩ }
  availability := { decide := fun _ => .unavailable ⟨fun h => h⟩ }
  tierOne := { certify := fun available => False.elim available.available }
  tierOneRouting := { route := fun {_} {available} _ => False.elim available.available }
  fallback := { certify := fun _ => ⟨trivial, trivial⟩ }
  reconciliation := { decide := fun _ => .reconciled ⟨trivial⟩ }
  comparison := { certify := fun _ => ⟨trivial, trivial⟩ }
  routing := { route := fun overlap => False.elim (overlap.unreconciled trivial) }

def overlapFramework : CT13.Framework :=
  { fallbackFramework with ResourcesReconciled := fun _ => False }
def overlapInput : CT13.Input overlapFramework := CT6CT10Fixtures.ct13Input
private def overlapBase
    (route : ∀ {scope : CT13.ScopedState overlapFramework overlapInput}
      {unavailable : CT13.UnavailableState overlapFramework overlapInput scope}
      {fallback : CT13.FallbackState overlapFramework overlapInput unavailable}
      (overlap : CT13.OverlapState overlapFramework overlapInput fallback),
      CT13.Nodes.Routing.Contract overlapFramework overlapInput overlap) :
    CT13.CorePlan overlapFramework overlapInput where
  scope := { decide := .ready ⟨trivial⟩ }
  availability := { decide := fun _ => .unavailable ⟨fun h => h⟩ }
  tierOne := { certify := fun available => False.elim available.available }
  tierOneRouting := { route := fun {_} {available} _ => False.elim available.available }
  fallback := { certify := fun _ => ⟨trivial, trivial⟩ }
  reconciliation := { decide := fun _ => .overlap ⟨fun h => h⟩ }
  comparison := { certify := fun reconciled => False.elim reconciled.reconciled }
  routing := { route := route }
def ct9Plan : CT13.CorePlan overlapFramework overlapInput := overlapBase
  (fun _ => .toCT9 { downstream := CT6CT10Fixtures.ct9Input, aligned := trivial })
def ct14Plan : CT13.CorePlan overlapFramework overlapInput := overlapBase
  (fun _ => .toCT14 { downstream := CT6CT10Fixtures.ct14Input, aligned := trivial })

def port : CT13.Port framework input where accepts := fun _ => True
def handoff : CT13.HandoffPlan framework input port where accept := fun _ => trivial
def ct4Result := CT13.runTraced framework input ct4Plan port handoff
def fallbackPort : CT13.Port fallbackFramework fallbackInput where accepts := fun _ => True
def fallbackHandoff : CT13.HandoffPlan fallbackFramework fallbackInput fallbackPort where
  accept := fun _ => trivial
def overlapPort : CT13.Port overlapFramework overlapInput where accepts := fun _ => True
def overlapHandoff : CT13.HandoffPlan overlapFramework overlapInput overlapPort where
  accept := fun _ => trivial
def c4Result := CT13.runTraced fallbackFramework fallbackInput c4Plan fallbackPort fallbackHandoff
def ct9Result := CT13.runTraced overlapFramework overlapInput ct9Plan overlapPort overlapHandoff
def ct14Result := CT13.runTraced overlapFramework overlapInput ct14Plan overlapPort overlapHandoff
theorem ct4_terminal : ct4Result.terminal = .ct4 := rfl
theorem c4_terminal : c4Result.terminal = .c4 := rfl
theorem ct9_terminal : ct9Result.terminal = .ct9 := rfl
theorem ct14_terminal : ct14Result.terminal = .ct14 := rfl
theorem ct4_trace : ct4Result.trace =
    [.entry, .scopeDecision, .availabilityDecision, .tierOneCertification,
      .tierOneRoutingCertification, .ct4Terminal] := rfl
theorem c4_trace : c4Result.trace =
    [.entry, .scopeDecision, .availabilityDecision, .fallbackCertification,
      .reconciliationDecision, .comparisonCertification, .c4Terminal] := rfl
theorem ct9_trace : ct9Result.trace =
    [.entry, .scopeDecision, .availabilityDecision, .fallbackCertification,
      .reconciliationDecision, .overlapRoutingDecision, .ct9Terminal] := rfl
theorem ct14_trace : ct14Result.trace =
    [.entry, .scopeDecision, .availabilityDecision, .fallbackCertification,
      .reconciliationDecision, .overlapRoutingDecision, .ct14Terminal] := rfl

def scopeEntry : CT13.Interface.Framework :=
  { CT6CT10Fixtures.ct13Entry with ScopeReady := fun _ _ _ _ => False }
def scopeFramework := mkFramework scopeEntry
def scopeInput : CT13.Input scopeFramework where
  G := (); branch := (); account := (); availability := (); resource := ()
def scopePlan : CT13.CorePlan scopeFramework scopeInput where
  scope := { decide := .exit ⟨fun h => h⟩ }
  availability := { decide := fun s => False.elim s.ready }
  tierOne := { certify := fun {scope} _ => False.elim scope.ready }
  tierOneRouting := { route := fun {scope} _ => False.elim scope.ready }
  fallback := { certify := fun {scope} _ => False.elim scope.ready }
  reconciliation := { decide := fun {scope} _ => False.elim scope.ready }
  comparison := { certify := fun {scope} _ => False.elim scope.ready }
  routing := { route := fun {scope} _ => False.elim scope.ready }
def scopePort : CT13.Port scopeFramework scopeInput where accepts := fun _ => True
def scopeHandoff : CT13.HandoffPlan scopeFramework scopeInput scopePort where accept := fun _ => trivial
def scopeResult := CT13.runTraced scopeFramework scopeInput scopePlan scopePort scopeHandoff
theorem scope_terminal : scopeResult.terminal = .scope := rfl
theorem scope_trace : scopeResult.trace = [.entry, .scopeDecision, .scopeTerminal] := rfl

example : CT13.OutcomeClaim ct4Result.outcome := by
  ct13 input using ct4Plan with port via handoff
example : ∃ result : CT13.ExecutionResult framework input port,
    CT13.OutcomeClaim result.outcome ∧ @CT13.Graph.ValidTrace framework input result.trace := by
  ct13_total input using ct4Plan with port via handoff
end StructuralExhaustion.Examples.CT13Toy
