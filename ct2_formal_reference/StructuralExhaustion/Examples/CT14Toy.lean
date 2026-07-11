import StructuralExhaustion.CT14.Automation
import StructuralExhaustion.Examples.CT6CT10Interfaces

namespace StructuralExhaustion.Examples.CT14Toy
open StructuralExhaustion

def mkFramework (entry : CT14.Interface.Framework) : CT14.Framework where
  entry := entry
  ct9 := CT6CT10Fixtures.ct9Entry
  ct10 := CT6CT10Fixtures.ct10Entry
  LowerBoundCertified := fun _ => True
  UpperBoundCertified := fun _ => True
  MultiplicityCounted := fun _ => True
  AggregateComparison := fun _ => True
  CT9Aligned := fun _ _ => True
  CT10Aligned := fun _ _ => True
def framework := mkFramework CT6CT10Fixtures.ct14Entry
def input : CT14.Input framework := CT6CT10Fixtures.ct14Input
private def bounds (scope : CT14.ScopedState framework input) :
    CT14.BoundsState framework input := ⟨scope, trivial, trivial⟩
private def counted (state : CT14.BoundsState framework input) :
    CT14.MultiplicityState framework input state := ⟨trivial⟩
private def makePlan
    (decide : ∀ state : CT14.BoundsState framework input,
      CT14.Nodes.Multiplicity.Contract framework input state) : CT14.CorePlan framework input where
  scope := { decide := .ready ⟨trivial⟩ }
  bounds := { certify := bounds }
  multiplicity := { decide := decide }
  comparison := { certify := fun _ => ⟨trivial, trivial⟩ }
def ct9Plan := makePlan (fun _state => .unbounded {
  downstream := CT6CT10Fixtures.ct9Input, aligned := trivial })
def ct10Plan := makePlan (fun _state => .missingLabel {
  downstream := CT6CT10Fixtures.ct10Input, aligned := trivial })
def c4Plan := makePlan (fun state => .counted (counted state))
def port : CT14.Port framework input where accepts := fun _ => True
def handoff : CT14.HandoffPlan framework input port where accept := fun _ => trivial
def ct9Result := CT14.runTraced framework input ct9Plan port handoff
def ct10Result := CT14.runTraced framework input ct10Plan port handoff
def c4Result := CT14.runTraced framework input c4Plan port handoff
theorem ct9_terminal : ct9Result.terminal = .ct9 := rfl
theorem ct10_terminal : ct10Result.terminal = .ct10 := rfl
theorem c4_terminal : c4Result.terminal = .c4 := rfl
theorem ct9_trace : ct9Result.trace =
    [.entry, .scopeDecision, .boundsCertification, .multiplicityDecision,
      .ct9Terminal] := rfl
theorem ct10_trace : ct10Result.trace =
    [.entry, .scopeDecision, .boundsCertification, .multiplicityDecision,
      .ct10Terminal] := rfl
theorem c4_trace : c4Result.trace =
    [.entry, .scopeDecision, .boundsCertification, .multiplicityDecision,
      .comparisonCertification, .c4Terminal] := rfl

def scopeEntry : CT14.Interface.Framework :=
  { CT6CT10Fixtures.ct14Entry with ScopeReady := fun _ _ _ _ _ => False }
def scopeFramework := mkFramework scopeEntry
def scopeInput : CT14.Input scopeFramework where
  G := (); branch := (); residual := (); lowerMass := (); capacity := (); multiplicity := ()
def scopePlan : CT14.CorePlan scopeFramework scopeInput where
  scope := { decide := .exit ⟨fun h => h⟩ }
  bounds := { certify := fun s => False.elim s.ready }
  multiplicity := { decide := fun s => False.elim s.scope.ready }
  comparison := { certify := fun {bounds} _ => False.elim bounds.scope.ready }
def scopePort : CT14.Port scopeFramework scopeInput where accepts := fun _ => True
def scopeHandoff : CT14.HandoffPlan scopeFramework scopeInput scopePort where accept := fun _ => trivial
def scopeResult := CT14.runTraced scopeFramework scopeInput scopePlan scopePort scopeHandoff
theorem scope_terminal : scopeResult.terminal = .scope := rfl
theorem scope_trace : scopeResult.trace = [.entry, .scopeDecision, .scopeTerminal] := rfl
example : CT14.OutcomeClaim c4Result.outcome := by
  ct14 input using c4Plan with port via handoff
example : ∃ result : CT14.ExecutionResult framework input port,
    CT14.OutcomeClaim result.outcome ∧ @CT14.Graph.ValidTrace framework input result.trace := by
  ct14_total input using c4Plan with port via handoff
end StructuralExhaustion.Examples.CT14Toy
