import StructuralExhaustion.CT15.Automation
import StructuralExhaustion.Examples.CT3Toy
import StructuralExhaustion.Examples.CT4Toy
import StructuralExhaustion.Examples.CT6CT10Interfaces

namespace StructuralExhaustion.Examples.CT15Toy
open StructuralExhaustion

def mkFramework (entry : CT15.Interface.Framework) : CT15.Framework where
  entry := entry
  ct3 := CT3Toy.framework
  ct4 := CT4Toy.framework
  ct7 := CT6CT10Fixtures.ct7Entry
  ct16 := CT6CT10Fixtures.ct16Entry
  TargetRelative := fun _ => True
  StructuralDependence := fun _ => True
  IndependentCoordinates := fun _ => True
  LedgerCertified := fun _ => True
  DemandExceedsCapacity := fun _ => True
  CT3Aligned := fun _ _ => True
  CT4Aligned := fun _ _ => True
  CT7Aligned := fun _ _ => True
  CT16Aligned := fun _ _ => True
def framework := mkFramework CT6CT10Fixtures.ct15Entry
def input : CT15.Input framework := CT6CT10Fixtures.ct15Input
private def rank (scope : CT15.ScopedState framework input) : CT15.RankState framework input :=
  ⟨scope, trivial⟩
private def dependence (state : CT15.RankState framework input) :
    CT15.DependenceState framework input state := ⟨trivial⟩
private def full (state : CT15.RankState framework input) :
    CT15.FullRankState framework input state := ⟨trivial⟩
private def makePlan
    (rankDrop : ∀ state : CT15.RankState framework input,
      CT15.Nodes.RankDrop.Contract framework input state)
    (route : ∀ {state : CT15.RankState framework input}
      (dep : CT15.DependenceState framework input state),
      CT15.Nodes.DependenceRouting.Contract framework input dep)
    (compare : ∀ {state : CT15.RankState framework input}
      {independent : CT15.FullRankState framework input state}
      (ledger : CT15.LedgerState framework input independent),
      CT15.Nodes.Comparison.Contract framework input ledger) : CT15.CorePlan framework input where
  scope := { decide := .ready ⟨trivial⟩ }
  rank := { certify := rank }
  rankDrop := { decide := rankDrop }
  dependenceRouting := { route := route }
  ledger := { certify := fun _ => ⟨trivial⟩ }
  comparison := { decide := compare }
private def dependentPlan
    (route : ∀ {state : CT15.RankState framework input}
      (dep : CT15.DependenceState framework input state),
      CT15.Nodes.DependenceRouting.Contract framework input dep) :=
  makePlan (fun state => .dependent (dependence state)) route
    (fun _ => .close ⟨trivial, trivial⟩)
def ct3Plan := dependentPlan (fun _ => .toCT3 {
  downstream := CT3Toy.input, aligned := trivial })
def ct7Plan := dependentPlan (fun _ => .toCT7 {
  downstream := CT6CT10Fixtures.ct7Input, aligned := trivial })
def ct16Plan := dependentPlan (fun _ => .toCT16 {
  downstream := CT6CT10Fixtures.ct16Input, aligned := trivial })
def c4Plan := makePlan (fun state => .full (full state))
  (fun _ => .toCT3 { downstream := CT3Toy.input, aligned := trivial })
  (fun _ => .close ⟨trivial, trivial⟩)
def ct4Plan := makePlan (fun state => .full (full state))
  (fun _ => .toCT3 { downstream := CT3Toy.input, aligned := trivial })
  (fun _ => .toCT4 { downstream := CT4Toy.input, aligned := trivial })
def port : CT15.Port framework input where accepts := fun _ => True
def handoff : CT15.HandoffPlan framework input port where accept := fun _ => trivial
def ct3Result := CT15.runTraced framework input ct3Plan port handoff
def ct7Result := CT15.runTraced framework input ct7Plan port handoff
def ct16Result := CT15.runTraced framework input ct16Plan port handoff
def c4Result := CT15.runTraced framework input c4Plan port handoff
def ct4Result := CT15.runTraced framework input ct4Plan port handoff
theorem ct3_terminal : ct3Result.terminal = .ct3 := rfl
theorem ct7_terminal : ct7Result.terminal = .ct7 := rfl
theorem ct16_terminal : ct16Result.terminal = .ct16 := rfl
theorem c4_terminal : c4Result.terminal = .c4 := rfl
theorem ct4_terminal : ct4Result.terminal = .ct4 := rfl
theorem ct3_trace : ct3Result.trace =
    [.entry, .scopeDecision, .rankCertification, .rankDropDecision,
      .dependenceRoutingDecision, .ct3Terminal] := rfl
theorem ct7_trace : ct7Result.trace =
    [.entry, .scopeDecision, .rankCertification, .rankDropDecision,
      .dependenceRoutingDecision, .ct7Terminal] := rfl
theorem ct16_trace : ct16Result.trace =
    [.entry, .scopeDecision, .rankCertification, .rankDropDecision,
      .dependenceRoutingDecision, .ct16Terminal] := rfl
theorem c4_trace : c4Result.trace =
    [.entry, .scopeDecision, .rankCertification, .rankDropDecision,
      .ledgerCertification, .comparisonDecision, .c4Terminal] := rfl
theorem ct4_trace : ct4Result.trace =
    [.entry, .scopeDecision, .rankCertification, .rankDropDecision,
      .ledgerCertification, .comparisonDecision, .ct4Terminal] := rfl

def scopeEntry : CT15.Interface.Framework :=
  { CT6CT10Fixtures.ct15Entry with ScopeReady := fun _ _ _ _ _ => False }
def scopeFramework := mkFramework scopeEntry
def scopeInput : CT15.Input scopeFramework where
  G := (); branch := (); tests := (); rankMap := (); target := (); capacity := ()
def scopePlan : CT15.CorePlan scopeFramework scopeInput where
  scope := { decide := .exit ⟨fun h => h⟩ }
  rank := { certify := fun s => False.elim s.ready }
  rankDrop := { decide := fun s => False.elim s.scope.ready }
  dependenceRouting := { route := fun {rank} _ => False.elim rank.scope.ready }
  ledger := { certify := fun {rank} _ => False.elim rank.scope.ready }
  comparison := { decide := fun {rank} _ => False.elim rank.scope.ready }
def scopePort : CT15.Port scopeFramework scopeInput where accepts := fun _ => True
def scopeHandoff : CT15.HandoffPlan scopeFramework scopeInput scopePort where accept := fun _ => trivial
def scopeResult := CT15.runTraced scopeFramework scopeInput scopePlan scopePort scopeHandoff
theorem scope_terminal : scopeResult.terminal = .scope := rfl
theorem scope_trace : scopeResult.trace = [.entry, .scopeDecision, .scopeTerminal] := rfl
example : CT15.OutcomeClaim c4Result.outcome := by
  ct15 input using c4Plan with port via handoff
example : ∃ result : CT15.ExecutionResult framework input port,
    CT15.OutcomeClaim result.outcome ∧ @CT15.Graph.ValidTrace framework input result.trace := by
  ct15_total input using c4Plan with port via handoff
end StructuralExhaustion.Examples.CT15Toy
