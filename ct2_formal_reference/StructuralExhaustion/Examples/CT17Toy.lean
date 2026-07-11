import StructuralExhaustion.CT17.Automation
import StructuralExhaustion.Examples.CT3Toy
import StructuralExhaustion.Examples.CT6CT10Interfaces

namespace StructuralExhaustion.Examples.CT17Toy
open StructuralExhaustion

def mkFramework (entry : CT17.Interface.Framework) : CT17.Framework where
  entry := entry
  ct3 := CT3Toy.framework
  ct8 := CT6CT10Fixtures.ct8Entry
  ct10 := CT6CT10Fixtures.ct10Entry
  ct14 := CT6CT10Fixtures.ct14Entry
  CompatibleOffsets := fun _ => True
  BlockCertified := fun _ => True
  FiniteRange := fun _ => True
  RepeatedIncrements := fun _ => True
  NoFiniteSurvivors := fun _ => True
  ArithmeticForcesTarget := fun _ => True
  CT3Aligned := fun _ _ => True
  CT8Aligned := fun _ _ => True
  CT10Aligned := fun _ _ => True
  CT14Aligned := fun _ _ => True
def framework := mkFramework CT6CT10Fixtures.ct17Entry
def input : CT17.Input framework := CT6CT10Fixtures.ct17Input
private def compatible (scope : CT17.ScopedState framework input) :
    CT17.CompatibleState framework input scope := ⟨trivial⟩
private def finite {scope : CT17.ScopedState framework input}
    {same : CT17.CompatibleState framework input scope}
    (block : CT17.BlockState framework input same) : CT17.FiniteState framework input block :=
  ⟨trivial⟩
private def repeated {scope : CT17.ScopedState framework input}
    {same : CT17.CompatibleState framework input scope}
    (block : CT17.BlockState framework input same) : CT17.RepeatedState framework input block :=
  ⟨trivial⟩
private def makePlan
    (scale : ∀ {scope : CT17.ScopedState framework input}
      {same : CT17.CompatibleState framework input scope}
      (block : CT17.BlockState framework input same),
      CT17.Nodes.Scale.Contract framework input block)
    (survivors : ∀ {scope : CT17.ScopedState framework input}
      {same : CT17.CompatibleState framework input scope}
      {block : CT17.BlockState framework input same}
      (finite : CT17.FiniteState framework input block),
      CT17.Nodes.Survivors.Contract framework input finite)
    (arithmetic : ∀ {scope : CT17.ScopedState framework input}
      {same : CT17.CompatibleState framework input scope}
      {block : CT17.BlockState framework input same}
      (repeated : CT17.RepeatedState framework input block),
      CT17.Nodes.Arithmetic.Contract framework input repeated) : CT17.CorePlan framework input where
  scope := { decide := .ready ⟨trivial⟩ }
  compatibility := { decide := fun scope => .compatible (compatible scope) }
  separation := { route := fun {_} state => False.elim (state.incompatible trivial) }
  block := { certify := fun _ => ⟨trivial⟩ }
  scale := { decide := scale }
  survivors := { decide := survivors }
  arithmetic := { decide := arithmetic }
def c5Plan := makePlan (fun block => .finite (finite block))
  (fun _ => .exhausted ⟨trivial, trivial⟩)
  (fun _ => .close ⟨trivial, trivial⟩)
def ct8Plan := makePlan (fun block => .finite (finite block))
  (fun _ => .persist { downstream := CT6CT10Fixtures.ct8Input, aligned := trivial })
  (fun _ => .close ⟨trivial, trivial⟩)
def c1Plan := makePlan (fun block => .repeated (repeated block))
  (fun _ => .exhausted ⟨trivial, trivial⟩)
  (fun _ => .close ⟨trivial, trivial⟩)
def ct14Plan := makePlan (fun block => .repeated (repeated block))
  (fun _ => .exhausted ⟨trivial, trivial⟩)
  (fun _ => .residual { downstream := CT6CT10Fixtures.ct14Input, aligned := trivial })
def port : CT17.Port framework input where accepts := fun _ => True
def handoff : CT17.HandoffPlan framework input port where accept := fun _ => trivial
def c5Result := CT17.runTraced framework input c5Plan port handoff
def ct8Result := CT17.runTraced framework input ct8Plan port handoff
def c1Result := CT17.runTraced framework input c1Plan port handoff
def ct14Result := CT17.runTraced framework input ct14Plan port handoff

def separationFramework : CT17.Framework :=
  { framework with CompatibleOffsets := fun _ => False }
def separationInput : CT17.Input separationFramework := CT6CT10Fixtures.ct17Input
private def separationPlan
    (route : ∀ {scope : CT17.ScopedState separationFramework separationInput}
      (state : CT17.IncompatibleState separationFramework separationInput scope),
      CT17.Nodes.Separation.Contract separationFramework separationInput state) :
    CT17.CorePlan separationFramework separationInput where
  scope := { decide := .ready ⟨trivial⟩ }
  compatibility := { decide := fun _ => .incompatible ⟨fun h => h⟩ }
  separation := { route := route }
  block := { certify := fun same => False.elim same.compatible }
  scale := { decide := fun {_} {compatible} _ => False.elim compatible.compatible }
  survivors := { decide := fun {_} {compatible} {_} _ => False.elim compatible.compatible }
  arithmetic := { decide := fun {_} {compatible} {_} _ => False.elim compatible.compatible }
def ct3Plan := separationPlan (fun _ => .toCT3 {
  downstream := CT3Toy.input, aligned := trivial })
def ct10Plan := separationPlan (fun _ => .toCT10 {
  downstream := CT6CT10Fixtures.ct10Input, aligned := trivial })
def separationPort : CT17.Port separationFramework separationInput where accepts := fun _ => True
def separationHandoff : CT17.HandoffPlan separationFramework separationInput separationPort where
  accept := fun _ => trivial
def ct3Result := CT17.runTraced separationFramework separationInput ct3Plan
  separationPort separationHandoff
def ct10Result := CT17.runTraced separationFramework separationInput ct10Plan
  separationPort separationHandoff

theorem c5_terminal : c5Result.terminal = .c5 := rfl
theorem ct8_terminal : ct8Result.terminal = .ct8 := rfl
theorem c1_terminal : c1Result.terminal = .c1 := rfl
theorem ct14_terminal : ct14Result.terminal = .ct14 := rfl
theorem ct3_terminal : ct3Result.terminal = .ct3 := rfl
theorem ct10_terminal : ct10Result.terminal = .ct10 := rfl
theorem c5_trace : c5Result.trace =
    [.entry, .scopeDecision, .compatibilityDecision, .blockCertification,
      .scaleDecision, .survivorsDecision, .c5Terminal] := rfl
theorem ct8_trace : ct8Result.trace =
    [.entry, .scopeDecision, .compatibilityDecision, .blockCertification,
      .scaleDecision, .survivorsDecision, .ct8Terminal] := rfl
theorem c1_trace : c1Result.trace =
    [.entry, .scopeDecision, .compatibilityDecision, .blockCertification,
      .scaleDecision, .arithmeticDecision, .c1Terminal] := rfl
theorem ct14_trace : ct14Result.trace =
    [.entry, .scopeDecision, .compatibilityDecision, .blockCertification,
      .scaleDecision, .arithmeticDecision, .ct14Terminal] := rfl
theorem ct3_trace : ct3Result.trace =
    [.entry, .scopeDecision, .compatibilityDecision, .separationDecision,
      .ct3Terminal] := rfl
theorem ct10_trace : ct10Result.trace =
    [.entry, .scopeDecision, .compatibilityDecision, .separationDecision,
      .ct10Terminal] := rfl

def scopeEntry : CT17.Interface.Framework :=
  { CT6CT10Fixtures.ct17Entry with ScopeReady := fun _ _ _ _ _ => False }
def scopeFramework := mkFramework scopeEntry
def scopeInput : CT17.Input scopeFramework where
  G := (); branch := (); targetSet := (); offsets := (); completions := (); arithmetic := ()
def scopePlan : CT17.CorePlan scopeFramework scopeInput where
  scope := { decide := .exit ⟨fun h => h⟩ }
  compatibility := { decide := fun s => False.elim s.ready }
  separation := { route := fun {scope} _ => False.elim scope.ready }
  block := { certify := fun {scope} _ => False.elim scope.ready }
  scale := { decide := fun {scope} _ => False.elim scope.ready }
  survivors := { decide := fun {scope} _ => False.elim scope.ready }
  arithmetic := { decide := fun {scope} _ => False.elim scope.ready }
def scopePort : CT17.Port scopeFramework scopeInput where accepts := fun _ => True
def scopeHandoff : CT17.HandoffPlan scopeFramework scopeInput scopePort where accept := fun _ => trivial
def scopeResult := CT17.runTraced scopeFramework scopeInput scopePlan scopePort scopeHandoff
theorem scope_terminal : scopeResult.terminal = .scope := rfl
theorem scope_trace : scopeResult.trace = [.entry, .scopeDecision, .scopeTerminal] := rfl
example : CT17.OutcomeClaim c1Result.outcome := by
  ct17 input using c1Plan with port via handoff
example : ∃ result : CT17.ExecutionResult framework input port,
    CT17.OutcomeClaim result.outcome ∧ @CT17.Graph.ValidTrace framework input result.trace := by
  ct17_total input using c1Plan with port via handoff
end StructuralExhaustion.Examples.CT17Toy
