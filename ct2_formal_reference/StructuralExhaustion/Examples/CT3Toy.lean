import StructuralExhaustion.CT3.Automation
import StructuralExhaustion.Examples.CT6CT10Interfaces

namespace StructuralExhaustion.Examples.CT3Toy

open StructuralExhaustion

def framework : CT3.Framework where
  Ambient := Unit
  BranchState := fun _ => Unit
  Piece := Unit
  Interface := Unit
  Context := Unit
  ExternalType := Unit
  interface := fun _ => ()
  externalType := fun _ => ()
  CertifiedInterface := fun _ => True
  TypeIndexFinite := fun _ => True
  Compatible := fun _ _ => True
  Response := fun _ _ => True
  TypeAccepts := fun _ _ => True
  TypeIncluded := fun _ _ => True
  ReplacementAdmissible := fun _ _ _ _ => True
  SmallerReplacement := fun _ _ _ _ => False
  ReplacementPreserves := fun _ _ _ _ => True
  TypeDataPersists := fun _ _ _ => True
  C2Claim := fun _ _ => True
  C3Claim := fun _ _ => True
  C5Claim := fun _ _ => True
  ct7 := CT6CT10Fixtures.ct7Entry
  ct8 := CT6CT10Fixtures.ct8Entry
  ct12 := CT6CT10Fixtures.ct12Entry
  CT7Aligned := fun _ _ _ _ => True
  CT8Aligned := fun _ _ _ _ => True
  CT12Aligned := fun _ _ _ _ => True

def input : CT3.Input framework where
  G := ()
  branch := ()
  X := ()
  certifiedInterface := trivial

private def equivalence
    (scope : CT3.ScopedState framework input) :
    CT3.EquivalenceState framework input where
  scope := scope
  certificate := {
    decidesResponses := fun _ _ => Iff.intro (fun _ => trivial) (fun _ => trivial)
  }

private theorem noReplacement :
    CT3.ReplacementWitness framework input → False :=
  fun witness => witness.smaller

private def residual
    (equiv : CT3.EquivalenceState framework input) :
    CT3.UncompressibleState framework input equiv where
  noReplacement := noReplacement

def port : CT3.Port framework input where
  accepts := fun _ => True

def handoff : CT3.HandoffPlan framework input port where
  accept := fun _ => trivial

private def basePlan
    (defect : ∀ {equiv : CT3.EquivalenceState framework input}
      (state : CT3.UncompressibleState framework input equiv),
      CT3.Nodes.Defect.Contract framework input state)
    (table : ∀ {equiv : CT3.EquivalenceState framework input}
      {state : CT3.UncompressibleState framework input equiv}
      (persistent : CT3.PersistentState framework input state),
      CT3.Nodes.Table.Contract framework input persistent) :
    CT3.CorePlan framework input where
  scope := { decide := .ready ⟨trivial⟩ }
  equivalence := { certify := equivalence }
  compression := { decide := fun equiv => .residual (residual equiv) }
  defect := { classify := defect }
  table := { classify := table }

def c3Plan : CT3.CorePlan framework input :=
  basePlan
    (fun _ => .close { closes := trivial })
    (fun _ => .close { closes := trivial })

def ct7Plan : CT3.CorePlan framework input :=
  basePlan
    (fun _ => .toCT7 {
      downstream := CT6CT10Fixtures.ct7Input
      aligned := trivial
    })
    (fun _ => .close { closes := trivial })

def ct12Plan : CT3.CorePlan framework input :=
  basePlan
    (fun _ => .toCT12 {
      downstream := CT6CT10Fixtures.ct12Input
      aligned := trivial
    })
    (fun _ => .close { closes := trivial })

def c5Plan : CT3.CorePlan framework input :=
  basePlan
    (fun _ => .persistent { persists := trivial })
    (fun _ => .close { closes := trivial })

def ct8Plan : CT3.CorePlan framework input :=
  basePlan
    (fun _ => .persistent { persists := trivial })
    (fun _ => .toCT8 {
      downstream := CT6CT10Fixtures.ct8Input
      aligned := trivial
    })

def c3Result := CT3.runTraced framework input c3Plan port handoff
def ct7Result := CT3.runTraced framework input ct7Plan port handoff
def ct12Result := CT3.runTraced framework input ct12Plan port handoff
def c5Result := CT3.runTraced framework input c5Plan port handoff
def ct8Result := CT3.runTraced framework input ct8Plan port handoff

theorem c3_terminal : c3Result.terminal = .c3 := rfl
theorem ct7_terminal : ct7Result.terminal = .ct7 := rfl
theorem ct12_terminal : ct12Result.terminal = .ct12 := rfl
theorem c5_terminal : c5Result.terminal = .c5 := rfl
theorem ct8_terminal : ct8Result.terminal = .ct8 := rfl

theorem c3_trace : c3Result.trace =
    [.entry, .scopeDecision, .equivalenceCertification,
      .compressionDecision, .defectDecision, .c3Terminal] := rfl
theorem ct7_trace : ct7Result.trace =
    [.entry, .scopeDecision, .equivalenceCertification,
      .compressionDecision, .defectDecision, .ct7Terminal] := rfl
theorem ct12_trace : ct12Result.trace =
    [.entry, .scopeDecision, .equivalenceCertification,
      .compressionDecision, .defectDecision, .ct12Terminal] := rfl
theorem c5_trace : c5Result.trace =
    [.entry, .scopeDecision, .equivalenceCertification,
      .compressionDecision, .defectDecision, .tableDecision, .c5Terminal] := rfl
theorem ct8_trace : ct8Result.trace =
    [.entry, .scopeDecision, .equivalenceCertification,
      .compressionDecision, .defectDecision, .tableDecision, .ct8Terminal] := rfl

/-! C2 compression terminal. -/

def compressionFramework : CT3.Framework :=
  { framework with SmallerReplacement := fun _ _ _ _ => True }

def compressionInput : CT3.Input compressionFramework where
  G := ()
  branch := ()
  X := ()
  certifiedInterface := trivial

private def compressionWitness :
    CT3.ReplacementWitness compressionFramework compressionInput where
  replacement := ()
  admissible := trivial
  smaller := trivial
  included := trivial
  preserves := trivial
  closes := trivial

def compressionPlan : CT3.CorePlan compressionFramework compressionInput where
  scope := { decide := .ready ⟨trivial⟩ }
  equivalence := {
    certify := fun scope => {
      scope := scope
      certificate := {
        decidesResponses := fun _ _ =>
          Iff.intro (fun _ => trivial) (fun _ => trivial)
      }
    }
  }
  compression := {
    decide := fun _ => .close { witness := compressionWitness }
  }
  defect := {
    classify := fun state => False.elim (state.noReplacement compressionWitness)
  }
  table := {
    classify := fun {_} {state} _ =>
      False.elim (state.noReplacement compressionWitness)
  }

def compressionPort : CT3.Port compressionFramework compressionInput where
  accepts := fun _ => True

def compressionHandoff :
    CT3.HandoffPlan compressionFramework compressionInput compressionPort where
  accept := fun _ => trivial

def c2Result :=
  CT3.runTraced compressionFramework compressionInput compressionPlan
    compressionPort compressionHandoff

theorem c2_terminal : c2Result.terminal = .c2 := rfl
theorem c2_trace : c2Result.trace =
    [.entry, .scopeDecision, .equivalenceCertification,
      .compressionDecision, .c2Terminal] := rfl

/-! Typed scope terminal. -/

def scopeFramework : CT3.Framework :=
  { framework with TypeIndexFinite := fun _ => False }

def scopeInput : CT3.Input scopeFramework where
  G := ()
  branch := ()
  X := ()
  certifiedInterface := trivial

def scopePlan : CT3.CorePlan scopeFramework scopeInput where
  scope := { decide := .exit ⟨fun finite => finite⟩ }
  equivalence := { certify := fun state => False.elim state.finiteIndex }
  compression := { decide := fun equiv => False.elim equiv.scope.finiteIndex }
  defect := {
    classify := fun {equivalence} _ =>
      False.elim equivalence.scope.finiteIndex
  }
  table := {
    classify := fun {equivalence} {_} _ =>
      False.elim equivalence.scope.finiteIndex
  }

def scopePort : CT3.Port scopeFramework scopeInput where
  accepts := fun _ => True

def scopeHandoff : CT3.HandoffPlan scopeFramework scopeInput scopePort where
  accept := fun _ => trivial

def scopeResult :=
  CT3.runTraced scopeFramework scopeInput scopePlan scopePort scopeHandoff

theorem scope_terminal : scopeResult.terminal = .scope := rfl
theorem scope_trace :
    scopeResult.trace = [.entry, .scopeDecision, .scopeTerminal] := rfl

example : CT3.OutcomeClaim ct8Result.outcome := by
  ct3 input using ct8Plan with port via handoff

example : ∃ result : CT3.ExecutionResult framework input port,
    CT3.OutcomeClaim result.outcome ∧
      @CT3.Graph.ValidTrace framework input result.trace := by
  ct3_total input using ct8Plan with port via handoff

end StructuralExhaustion.Examples.CT3Toy
