import StructuralExhaustion.CT1.Automation
import StructuralExhaustion.Examples.CT2Toy
import StructuralExhaustion.Examples.CT5Toy
import StructuralExhaustion.Examples.CT6CT10Interfaces

namespace StructuralExhaustion.Examples.CT1Toy

open StructuralExhaustion
open StructuralExhaustion.Examples

/-! ## The six target-avoiding routes -/

/-- A model with a ready scope, no realized test, and a false target. -/
def routingFramework : CT1.Framework where
  ct2 := CT2Toy.framework
  ct5 := CT5Toy.framework
  ct6 := CT6CT10Fixtures.ct6Entry
  ct17 := CT6CT10Fixtures.ct17Entry
  BranchState := fun _ => Unit
  TestIndex := Unit
  Witness := fun _ _ _ => Unit
  Realizes := fun _ _ _ _ => False
  ScopeReady := fun _ _ => True
  CT3Aligned := fun _ _ _ => True
  CT4Aligned := fun _ _ _ => True
  CT5Aligned := fun _ _ _ => True
  CT6Aligned := fun _ _ _ => True
  CT17Aligned := fun _ _ _ => True

def routingInput : CT1.Input routingFramework where
  G := ()
  branch := ()
  baseline := trivial

private def routingEquivalence
    (scopeState : CT1.ScopedState routingFramework routingInput) :
    CT1.EquivalenceState routingFramework routingInput where
  scope := scopeState
  certificate := {
    targetOfRealization := fun realization => False.elim realization.realizes
    realizationOfTarget := fun target => False.elim target
  }

private def routingAvoiding
    (equivalence : CT1.EquivalenceState routingFramework routingInput) :
    CT1.AvoidingState routingFramework routingInput :=
  CT1.AvoidingState.ofNoRealization equivalence
    (fun realization => realization.realizes)

private def ct2Payload
    (avoiding : CT1.AvoidingState routingFramework routingInput) :
    CT1.CT2Payload routingFramework routingInput avoiding where
  X := ()
  excludesSmaller := by
    intro _ smaller
    exact False.elim smaller
  proper := trivial
  admissible := trivial

private def routingPlan
    (classify : ∀ avoiding : CT1.AvoidingState routingFramework routingInput,
      CT1.Nodes.Payload.Decision routingFramework routingInput avoiding) :
    CT1.CorePlan routingFramework routingInput where
  scope := { decide := .ready ⟨trivial⟩ }
  equivalence := { certify := routingEquivalence }
  realization := { decide := fun equivalence => .avoiding (routingAvoiding equivalence) }
  payload := { classify := classify }

def permissivePort {F : CT1.Framework} (input : CT1.Input F) :
    CT1.Port F input where
  accepts := fun _ => True

def permissiveHandoff {F : CT1.Framework} (input : CT1.Input F) :
    CT1.HandoffPlan F input (permissivePort input) where
  accept := fun _ => trivial

def ct2Plan : CT1.CorePlan routingFramework routingInput :=
  routingPlan (fun avoiding => .toCT2 (ct2Payload avoiding))

def ct3Plan : CT1.CorePlan routingFramework routingInput :=
  routingPlan (fun _ => .toCT3 {
    downstream := CT3Toy.input
    aligned := trivial
  })

def ct4Plan : CT1.CorePlan routingFramework routingInput :=
  routingPlan (fun _ => .toCT4 {
    downstream := CT4Toy.input
    aligned := trivial
  })

def ct5Plan : CT1.CorePlan routingFramework routingInput :=
  routingPlan (fun _ => .toCT5 {
    downstream := CT5Toy.input
    aligned := trivial
  })

def ct6Plan : CT1.CorePlan routingFramework routingInput :=
  routingPlan (fun _ => .toCT6 {
    downstream := CT6CT10Fixtures.ct6Input
    aligned := trivial
  })

def ct17Plan : CT1.CorePlan routingFramework routingInput :=
  routingPlan (fun _ => .toCT17 {
    downstream := CT6CT10Fixtures.ct17Input
    aligned := trivial
  })

def routingPort : CT1.Port routingFramework routingInput :=
  permissivePort routingInput

def routingHandoff : CT1.HandoffPlan routingFramework routingInput routingPort :=
  permissiveHandoff routingInput

def ct2Result : CT1.ExecutionResult routingFramework routingInput routingPort :=
  CT1.runTraced routingFramework routingInput ct2Plan routingPort routingHandoff

def ct3Result : CT1.ExecutionResult routingFramework routingInput routingPort :=
  CT1.runTraced routingFramework routingInput ct3Plan routingPort routingHandoff

def ct4Result : CT1.ExecutionResult routingFramework routingInput routingPort :=
  CT1.runTraced routingFramework routingInput ct4Plan routingPort routingHandoff

def ct5Result : CT1.ExecutionResult routingFramework routingInput routingPort :=
  CT1.runTraced routingFramework routingInput ct5Plan routingPort routingHandoff

def ct6Result : CT1.ExecutionResult routingFramework routingInput routingPort :=
  CT1.runTraced routingFramework routingInput ct6Plan routingPort routingHandoff

def ct17Result : CT1.ExecutionResult routingFramework routingInput routingPort :=
  CT1.runTraced routingFramework routingInput ct17Plan routingPort routingHandoff

theorem ct2_terminal : ct2Result.terminal = .ct2 := rfl
theorem ct3_terminal : ct3Result.terminal = .ct3 := rfl
theorem ct4_terminal : ct4Result.terminal = .ct4 := rfl
theorem ct5_terminal : ct5Result.terminal = .ct5 := rfl
theorem ct6_terminal : ct6Result.terminal = .ct6 := rfl
theorem ct17_terminal : ct17Result.terminal = .ct17 := rfl

theorem ct2_trace :
    ct2Result.trace =
      [.entry, .scopeDecision, .equivalenceCertification,
        .realizationDecision, .payloadDecision, .ct2Terminal] := rfl

theorem ct3_trace :
    ct3Result.trace =
      [.entry, .scopeDecision, .equivalenceCertification,
        .realizationDecision, .payloadDecision, .ct3Terminal] := rfl

theorem ct4_trace :
    ct4Result.trace =
      [.entry, .scopeDecision, .equivalenceCertification,
        .realizationDecision, .payloadDecision, .ct4Terminal] := rfl

theorem ct5_trace :
    ct5Result.trace =
      [.entry, .scopeDecision, .equivalenceCertification,
        .realizationDecision, .payloadDecision, .ct5Terminal] := rfl

theorem ct6_trace :
    ct6Result.trace =
      [.entry, .scopeDecision, .equivalenceCertification,
        .realizationDecision, .payloadDecision, .ct6Terminal] := rfl

theorem ct17_trace :
    ct17Result.trace =
      [.entry, .scopeDecision, .equivalenceCertification,
        .realizationDecision, .payloadDecision, .ct17Terminal] := rfl

example : CT1.OutcomeClaim ct2Result.outcome := by
  ct1 routingInput using ct2Plan with routingPort via routingHandoff

example : ∃ result : CT1.ExecutionResult routingFramework routingInput routingPort,
    CT1.OutcomeClaim result.outcome ∧
      @CT1.Graph.ValidTrace routingFramework routingInput result.trace := by
  ct1_total routingInput using ct2Plan with routingPort via routingHandoff

/-! ## C1 closure -/

def hitCT2Framework : CT2.Framework :=
  { CT2Toy.framework with Target := fun _ => True }

def hitFramework : CT1.Framework where
  ct2 := hitCT2Framework
  ct5 := CT5Toy.framework
  ct6 := CT6CT10Fixtures.ct6Entry
  ct17 := CT6CT10Fixtures.ct17Entry
  BranchState := fun _ => Unit
  TestIndex := Unit
  Witness := fun _ _ _ => Unit
  Realizes := fun _ _ _ _ => True
  ScopeReady := fun _ _ => True
  CT3Aligned := fun _ _ _ => True
  CT4Aligned := fun _ _ _ => True
  CT5Aligned := fun _ _ _ => True
  CT6Aligned := fun _ _ _ => True
  CT17Aligned := fun _ _ _ => True

def hitInput : CT1.Input hitFramework where
  G := ()
  branch := ()
  baseline := trivial

private def hitRealization : CT1.TestRealization hitFramework hitInput where
  index := ()
  witness := ()
  realizes := trivial

private def hitEquivalence
    (scopeState : CT1.ScopedState hitFramework hitInput) :
    CT1.EquivalenceState hitFramework hitInput where
  scope := scopeState
  certificate := {
    targetOfRealization := fun _ => trivial
    realizationOfTarget := fun _ => ⟨hitRealization⟩
  }

def hitPlan : CT1.CorePlan hitFramework hitInput where
  scope := { decide := .ready ⟨trivial⟩ }
  equivalence := { certify := hitEquivalence }
  realization := {
    decide := fun equivalence => .hit {
      equivalence := equivalence
      realization := hitRealization
    }
  }
  payload := {
    classify := fun avoiding => False.elim (avoiding.targetAvoiding trivial)
  }

def hitPort : CT1.Port hitFramework hitInput := permissivePort hitInput

def hitHandoff : CT1.HandoffPlan hitFramework hitInput hitPort :=
  permissiveHandoff hitInput

def hitResult : CT1.ExecutionResult hitFramework hitInput hitPort :=
  CT1.runTraced hitFramework hitInput hitPlan hitPort hitHandoff

theorem hit_terminal : hitResult.terminal = .c1 := rfl

theorem hit_trace :
    hitResult.trace =
      [.entry, .scopeDecision, .equivalenceCertification,
        .realizationDecision, .c1Terminal] := rfl

theorem hit_closes_target : hitCT2Framework.Target hitInput.G :=
  hitResult.verified

/-! ## Typed scope exit -/

def scopeFramework : CT1.Framework :=
  { routingFramework with ScopeReady := fun _ _ => False }

def scopeInput : CT1.Input scopeFramework where
  G := ()
  branch := ()
  baseline := trivial

def scopePlan : CT1.CorePlan scopeFramework scopeInput where
  scope := { decide := .exit { unavailable := fun ready => ready } }
  equivalence := { certify := fun state => False.elim state.ready }
  realization := {
    decide := fun equivalence => False.elim equivalence.scope.ready
  }
  payload := {
    classify := fun avoiding => False.elim avoiding.equivalence.scope.ready
  }

def scopePort : CT1.Port scopeFramework scopeInput := permissivePort scopeInput

def scopeHandoff : CT1.HandoffPlan scopeFramework scopeInput scopePort :=
  permissiveHandoff scopeInput

def scopeResult : CT1.ExecutionResult scopeFramework scopeInput scopePort :=
  CT1.runTraced scopeFramework scopeInput scopePlan scopePort scopeHandoff

theorem scope_terminal : scopeResult.terminal = .scope := rfl

theorem scope_trace :
    scopeResult.trace = [.entry, .scopeDecision, .scopeTerminal] := rfl

/-! ## Exact direct adapters to CT3, CT4, and CT5 -/

def ct3DownstreamInput : CT3.Input CT3Toy.framework :=
  match ct3Result.outcome with
  | .ct3 payload _ => payload.toInput

def ct4DownstreamInput : CT4.Input CT4Toy.framework :=
  match ct4Result.outcome with
  | .ct4 payload _ => payload.toInput

def ct5DownstreamInput : CT5.Input CT5Toy.framework :=
  match ct5Result.outcome with
  | .ct5 payload _ => payload.toInput

theorem ct3_adapter_exact : ct3DownstreamInput = CT3Toy.input := rfl
theorem ct4_adapter_exact : ct4DownstreamInput = CT4Toy.input := rfl
theorem ct5_adapter_exact : ct5DownstreamInput = CT5Toy.input := rfl

def directCT3Result :
    CT3.ExecutionResult CT3Toy.framework ct3DownstreamInput CT3Toy.port :=
  CT3.runTraced CT3Toy.framework ct3DownstreamInput CT3Toy.ct8Plan
    CT3Toy.port CT3Toy.handoff

def directCT4Result :
    CT4.ExecutionResult CT4Toy.framework ct4DownstreamInput CT4Toy.port :=
  CT4.runTraced CT4Toy.framework ct4DownstreamInput CT4Toy.c4Plan
    CT4Toy.port CT4Toy.handoff

def directCT5Result :
    CT5.ExecutionResult CT5Toy.framework ct5DownstreamInput CT5Toy.port :=
  CT5.runTraced CT5Toy.framework ct5DownstreamInput CT5Toy.c4Plan
    CT5Toy.port CT5Toy.handoff

theorem direct_ct3_terminal : directCT3Result.terminal = .ct8 := rfl
theorem direct_ct4_terminal : directCT4Result.terminal = .c4 := rfl
theorem direct_ct5_terminal : directCT5Result.terminal = .c4 := rfl

/-! ## The exact CT1 to CT2 adapter -/

/-- This is the precise downstream input extracted from the executed CT1
CT2 terminal, rather than a separately reconstructed payload. -/
def downstreamInput : CT2.Input CT2Toy.framework :=
  match ct2Result.outcome with
  | .ct2 payload _ => payload.toInput

private theorem downstreamNoDeletion :
    CT2.DeletionWitness CT2Toy.framework downstreamInput → False :=
  fun witness => witness.smaller

private theorem downstreamNoCandidate :
    CT2.SmallerReplacementCandidate CT2Toy.framework downstreamInput → False :=
  fun candidate => candidate.smaller

def downstreamPlan : CT2.CorePlan CT2Toy.framework downstreamInput where
  interface := { decide := .bounded ⟨trivial⟩ }
  deletion := {
    decide := fun bounded => .critical {
      bounded := bounded
      critical := downstreamNoDeletion
    }
  }
  replacementCandidate := {
    search := fun critical => .absent {
      deletionCritical := critical
      targetUncompressible := downstreamNoCandidate
    }
  }
  context := {
    certify := fun state => False.elim (downstreamNoCandidate state.candidate)
  }
  survivor := {
    classify := fun _ => .criticality {
      datum := ()
      downstream := CT6CT10Fixtures.ct10Input
      aligned := trivial
    }
  }

def downstreamPort : CT2.Port CT2Toy.framework downstreamInput where
  ct3Accepts := fun _ => True
  ct10Accepts := fun _ => True

def downstreamHandoff :
    CT2.HandoffPlan CT2Toy.framework downstreamInput downstreamPort where
  acceptCT3 := fun _ => trivial
  acceptCT10 := fun _ => trivial

def downstreamResult :
    CT2.ExecutionResult CT2Toy.framework downstreamInput downstreamPort :=
  CT2.runTraced CT2Toy.framework downstreamInput downstreamPlan
    downstreamPort downstreamHandoff

theorem adapter_preserves_ambient : downstreamInput.G = routingInput.G := rfl

theorem downstream_terminal :
    downstreamResult.terminal = .criticalityCT10 := rfl

theorem downstream_trace :
    downstreamResult.trace =
      [.entry, .interfaceDecision, .deletionDecision,
        .replacementCandidateSearch, .survivorClassification,
        .criticalityCT10Terminal] := rfl

end StructuralExhaustion.Examples.CT1Toy
