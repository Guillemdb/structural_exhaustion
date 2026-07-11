import StructuralExhaustion.CT10.Automation
import StructuralExhaustion.Examples.CT6CT10Fixtures

namespace StructuralExhaustion.Examples.CT10Toy

open StructuralExhaustion

def mkFramework (entry : CT10.Interface.Framework) : CT10.Framework where
  entry := entry
  ct3 := CT3Toy.framework
  ct7 := CT6CT10Fixtures.ct7Entry
  ct15 := CT6CT10Fixtures.ct15Entry
  LabelClassesExhaust := fun _ => True
  ExchangeSupportFinite := fun _ => True
  DirectClassified := fun _ => True
  MissingDatumExtracted := fun _ => True
  PromotionCertified := fun _ => True
  CT3Aligned := fun _ _ => True
  CT7Aligned := fun _ _ => True
  CT15Aligned := fun _ _ => True

def framework := mkFramework CT6CT10Fixtures.ct10Entry
def input : CT10.Input framework := CT6CT10Fixtures.ct10Input

private def labels (scope : CT10.ScopedState framework input) :
    CT10.LabelState framework input where
  scope := scope
  certificate := ⟨trivial, trivial⟩
private def direct (state : CT10.LabelState framework input) :
    CT10.DirectState framework input state := ⟨trivial⟩
private def missing (state : CT10.LabelState framework input) :
    CT10.MissingState framework input state := ⟨trivial⟩
private def promoted {state : CT10.LabelState framework input}
    (gap : CT10.MissingState framework input state) :
    CT10.PromotedState framework input gap := ⟨trivial⟩

private def makePlan
    (classification : ∀ state : CT10.LabelState framework input,
      CT10.Nodes.Classification.Contract framework input state)
    (directRoute : ∀ {state : CT10.LabelState framework input}
      (classified : CT10.DirectState framework input state),
      CT10.Nodes.Direct.Contract framework input classified)
    (promotedRoute : ∀ {state : CT10.LabelState framework input}
      {gap : CT10.MissingState framework input state}
      (next : CT10.PromotedState framework input gap),
      CT10.Nodes.PromotedRouting.Contract framework input next) :
    CT10.CorePlan framework input where
  scope := { decide := .ready ⟨trivial⟩ }
  labels := { certify := labels }
  classification := { decide := classification }
  direct := { route := directRoute }
  promotion := { certify := promoted }
  promotedRouting := { route := promotedRoute }

def c5Plan : CT10.CorePlan framework input :=
  makePlan (fun _state => .close { closes := trivial })
    (fun _classified => .toCT3 {
      downstream := CT3Toy.input, aligned := trivial })
    (fun _next => .toCT15 {
      downstream := CT6CT10Fixtures.ct15Input, aligned := trivial })
def ct3DirectPlan : CT10.CorePlan framework input :=
  makePlan (fun state => .direct (direct state))
    (fun _ => .toCT3 { downstream := CT3Toy.input, aligned := trivial })
    (fun _ => .toCT15 {
      downstream := CT6CT10Fixtures.ct15Input, aligned := trivial })
def ct7Plan : CT10.CorePlan framework input :=
  makePlan (fun state => .direct (direct state))
    (fun _ => .toCT7 {
      downstream := CT6CT10Fixtures.ct7Input, aligned := trivial })
    (fun _ => .toCT15 {
      downstream := CT6CT10Fixtures.ct15Input, aligned := trivial })
def ct3PromotedPlan : CT10.CorePlan framework input :=
  makePlan (fun state => .missing (missing state))
    (fun _ => .toCT3 { downstream := CT3Toy.input, aligned := trivial })
    (fun _ => .toCT3 { downstream := CT3Toy.input, aligned := trivial })
def ct15Plan : CT10.CorePlan framework input :=
  makePlan (fun state => .missing (missing state))
    (fun _ => .toCT3 { downstream := CT3Toy.input, aligned := trivial })
    (fun _ => .toCT15 {
      downstream := CT6CT10Fixtures.ct15Input, aligned := trivial })

def port : CT10.Port framework input where accepts := fun _ => True
def handoff : CT10.HandoffPlan framework input port where accept := fun _ => trivial
def c5Result := CT10.runTraced framework input c5Plan port handoff
def ct3DirectResult := CT10.runTraced framework input ct3DirectPlan port handoff
def ct7Result := CT10.runTraced framework input ct7Plan port handoff
def ct3PromotedResult := CT10.runTraced framework input ct3PromotedPlan port handoff
def ct15Result := CT10.runTraced framework input ct15Plan port handoff
theorem c5_terminal : c5Result.terminal = .c5 := rfl
theorem ct3_direct_terminal : ct3DirectResult.terminal = .ct3 := rfl
theorem ct7_terminal : ct7Result.terminal = .ct7 := rfl
theorem ct3_promoted_terminal : ct3PromotedResult.terminal = .ct3 := rfl
theorem ct15_terminal : ct15Result.terminal = .ct15 := rfl
theorem c5_trace : c5Result.trace =
    [.entry, .scopeDecision, .labelCertification, .classificationDecision,
      .c5Terminal] := rfl
theorem ct3_direct_trace : ct3DirectResult.trace =
    [.entry, .scopeDecision, .labelCertification, .classificationDecision,
      .directDecision, .ct3Terminal] := rfl
theorem ct7_trace : ct7Result.trace =
    [.entry, .scopeDecision, .labelCertification, .classificationDecision,
      .directDecision, .ct7Terminal] := rfl
theorem ct3_promoted_trace : ct3PromotedResult.trace =
    [.entry, .scopeDecision, .labelCertification, .classificationDecision,
      .promotionCertification, .promotedRoutingDecision, .ct3Terminal] := rfl
theorem ct15_trace : ct15Result.trace =
    [.entry, .scopeDecision, .labelCertification, .classificationDecision,
      .promotionCertification, .promotedRoutingDecision, .ct15Terminal] := rfl

def scopeEntry : CT10.Interface.Framework :=
  { CT6CT10Fixtures.ct10Entry with ScopeReady := fun _ _ _ _ _ => False }
def scopeFramework := mkFramework scopeEntry
def scopeInput : CT10.Input scopeFramework where
  G := (); branch := (); residual := (); datum := (); alphabet := (); table := ()
def scopePlan : CT10.CorePlan scopeFramework scopeInput where
  scope := { decide := .exit ⟨fun ready => ready⟩ }
  labels := { certify := fun state => False.elim state.ready }
  classification := { decide := fun state => False.elim state.scope.ready }
  direct := { route := fun {labels} _ => False.elim labels.scope.ready }
  promotion := { certify := fun {labels} _ => False.elim labels.scope.ready }
  promotedRouting := { route := fun {labels} _ => False.elim labels.scope.ready }
def scopePort : CT10.Port scopeFramework scopeInput where accepts := fun _ => True
def scopeHandoff : CT10.HandoffPlan scopeFramework scopeInput scopePort where
  accept := fun _ => trivial
def scopeResult := CT10.runTraced scopeFramework scopeInput scopePlan scopePort scopeHandoff
theorem scope_terminal : scopeResult.terminal = .scope := rfl
theorem scope_trace : scopeResult.trace = [.entry, .scopeDecision, .scopeTerminal] := rfl

example : CT10.OutcomeClaim c5Result.outcome := by
  ct10 input using c5Plan with port via handoff
example : ∃ result : CT10.ExecutionResult framework input port,
    CT10.OutcomeClaim result.outcome ∧ @CT10.Graph.ValidTrace framework input result.trace := by
  ct10_total input using c5Plan with port via handoff

end StructuralExhaustion.Examples.CT10Toy
