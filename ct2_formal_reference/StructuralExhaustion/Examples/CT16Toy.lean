import StructuralExhaustion.CT16.Automation
import StructuralExhaustion.Examples.CT3Toy
import StructuralExhaustion.Examples.CT6CT10Interfaces

namespace StructuralExhaustion.Examples.CT16Toy
open StructuralExhaustion

def mkFramework (entry : CT16.Interface.Framework) : CT16.Framework where
  entry := entry
  ct3 := CT3Toy.framework
  ct10 := CT6CT10Fixtures.ct10Entry
  ProperSupport := fun _ => True
  WholeSupport := fun _ => True
  ClosedTypeComputed := fun _ => True
  NoSilentIdentification := fun _ => True
  LiteralEquality := fun _ => True
  CT3Aligned := fun _ _ => True
  CT10Aligned := fun _ _ => True
def framework := mkFramework CT6CT10Fixtures.ct16Entry
def input : CT16.Input framework := CT6CT10Fixtures.ct16Input
private def whole : CT16.WholeState framework input := ⟨trivial⟩
private def makeWholePlan
    (equality : ∀ {whole : CT16.WholeState framework input}
      {scope : CT16.ScopedState framework input whole}
      (closed : CT16.ClosedTypeState framework input scope),
      CT16.Nodes.Equality.Contract framework input closed) : CT16.CorePlan framework input where
  support := { decide := .whole whole }
  scope := { decide := fun _whole => .ready ⟨trivial⟩ }
  closedType := { certify := fun _ => ⟨trivial, trivial⟩ }
  equality := { decide := equality }
def ct3Plan : CT16.CorePlan framework input where
  support := { decide := .proper (state := ⟨trivial⟩) {
    downstream := CT3Toy.input, aligned := trivial } }
  scope := { decide := fun _ => .ready ⟨trivial⟩ }
  closedType := { certify := fun _ => ⟨trivial, trivial⟩ }
  equality := { decide := fun _ => .equal ⟨trivial, trivial⟩ }
def c2Plan := makeWholePlan (fun _ => .equal ⟨trivial, trivial⟩)
def ct10Plan := makeWholePlan (fun _ => .distinct {
  downstream := CT6CT10Fixtures.ct10Input, aligned := trivial })
def port : CT16.Port framework input where accepts := fun _ => True
def handoff : CT16.HandoffPlan framework input port where accept := fun _ => trivial
def ct3Result := CT16.runTraced framework input ct3Plan port handoff
def c2Result := CT16.runTraced framework input c2Plan port handoff
def ct10Result := CT16.runTraced framework input ct10Plan port handoff
theorem ct3_terminal : ct3Result.terminal = .ct3 := rfl
theorem c2_terminal : c2Result.terminal = .c2 := rfl
theorem ct10_terminal : ct10Result.terminal = .ct10 := rfl
theorem ct3_trace : ct3Result.trace = [.entry, .supportDecision, .ct3Terminal] := rfl
theorem c2_trace : c2Result.trace =
    [.entry, .supportDecision, .scopeDecision, .closedTypeCertification,
      .equalityDecision, .c2Terminal] := rfl
theorem ct10_trace : ct10Result.trace =
    [.entry, .supportDecision, .scopeDecision, .closedTypeCertification,
      .equalityDecision, .ct10Terminal] := rfl

def scopeEntry : CT16.Interface.Framework :=
  { CT6CT10Fixtures.ct16Entry with ScopeReady := fun _ _ _ _ => False }
def scopeFramework := mkFramework scopeEntry
def scopeInput : CT16.Input scopeFramework where
  G := (); branch := (); support := (); datum := (); closedType := ()
def scopePlan : CT16.CorePlan scopeFramework scopeInput where
  support := { decide := .whole ⟨trivial⟩ }
  scope := { decide := fun _ => .exit ⟨fun h => h⟩ }
  closedType := { certify := fun s => False.elim s.ready }
  equality := { decide := fun {_} {scope} _ => False.elim scope.ready }
def scopePort : CT16.Port scopeFramework scopeInput where accepts := fun _ => True
def scopeHandoff : CT16.HandoffPlan scopeFramework scopeInput scopePort where accept := fun _ => trivial
def scopeResult := CT16.runTraced scopeFramework scopeInput scopePlan scopePort scopeHandoff
theorem scope_terminal : scopeResult.terminal = .scope := rfl
theorem scope_trace : scopeResult.trace =
    [.entry, .supportDecision, .scopeDecision, .scopeTerminal] := rfl
example : CT16.OutcomeClaim c2Result.outcome := by
  ct16 input using c2Plan with port via handoff
example : ∃ result : CT16.ExecutionResult framework input port,
    CT16.OutcomeClaim result.outcome ∧ @CT16.Graph.ValidTrace framework input result.trace := by
  ct16_total input using c2Plan with port via handoff
end StructuralExhaustion.Examples.CT16Toy
