import Hypostructure.Graph.CT1

/-!
# CT1 vertical-slice fixtures

The neutral fixtures exercise both deterministic branches on literal ledger
inputs.  The graph fixtures validate an explicit K4 cycle certificate and its
rooted-return encoding without enumerating walks, subgraphs, or ambient graphs.
-/

namespace Hypostructure.Fixtures.CT1

namespace Neutral

structure Residual where
  candidates : Core.Finite.Enumeration Bool
  card_le_two : candidates.card <= 2

abbrev Previous := Core.Residual.Ledger Residual

def spec : _root_.Hypostructure.CT1.Spec Previous where
  Candidate := fun _previous => Bool
  Realizes := fun _previous candidate => candidate = true

def schedule : Core.Residual.Query Previous fun previous =>
    Core.Finite.Enumeration (spec.Candidate previous) :=
  (Core.Residual.Query.residual (Source := Previous) (Residual := Residual)).map
    fun _previous residual => residual.candidates

def capability : _root_.Hypostructure.CT1.Capability spec where
  schedule := schedule
  realizesDecidable := fun _previous candidate => Bool.decEq candidate true
  inputSize := fun _previous => 0
  workCoefficient := 2
  workDegree := 0
  workBound := by
    intro previous
    change (Core.Residual.residualOf previous).candidates.card <= 2
    exact (Core.Residual.residualOf previous).card_le_two

def hitResidual : Residual where
  candidates := Core.Finite.Enumeration.ofNodupList [false, true] (by decide)
  card_le_two := by decide

def hitPrevious : Previous := Core.Residual.Ledger.initial hitResidual

def hitResult : _root_.Hypostructure.CT1.ExecutionResult spec capability :=
  _root_.Hypostructure.CT1.execute spec capability hitPrevious

theorem hit_previous : hitResult.stage.previous = hitPrevious := rfl

theorem hit_terminal : hitResult.terminal = .c1 := rfl

theorem hit_checks : hitResult.checks = 2 := rfl

theorem hit_trace :
    hitResult.traceNodes =
      [.entry, .schedule, .realizationDecision, .c1Terminal] :=
  rfl

theorem hit_target :
    _root_.Hypostructure.CT1.Target spec hitPrevious
      (capability.scheduleAt hitPrevious) :=
  hitResult.verified

theorem hit_work :
    hitResult.checks <= capability.workCoefficient *
      (capability.inputSize hitPrevious + 1) ^ capability.workDegree :=
  hitResult.checks_le_polynomial

def missResidual : Residual where
  candidates := Core.Finite.Enumeration.singleton false
  card_le_two := by decide

def missPrevious : Previous := Core.Residual.Ledger.initial missResidual

def missResult : _root_.Hypostructure.CT1.ExecutionResult spec capability :=
  _root_.Hypostructure.CT1.execute spec capability missPrevious

theorem miss_previous : missResult.stage.previous = missPrevious := rfl

theorem miss_terminal : missResult.terminal = .avoiding := rfl

theorem miss_checks : missResult.checks = 1 := rfl

theorem miss_trace :
    missResult.traceNodes =
      [.entry, .schedule, .realizationDecision, .avoidingTerminal] :=
  rfl

theorem miss_avoids :
    Not (_root_.Hypostructure.CT1.Target spec missPrevious
      (capability.scheduleAt missPrevious)) :=
  missResult.verified

theorem miss_work :
    missResult.checks <= capability.workCoefficient *
      (capability.inputSize missPrevious + 1) ^ capability.workDegree :=
  missResult.checks_le_polynomial

end Neutral

namespace CertificateMode

structure Residual where
  enabled : Bool

abbrev Previous := Core.Residual.Ledger Residual

def PublicTarget (previous : Previous) : Prop :=
  (Core.Residual.residualOf previous).enabled = true

/-- A dependent proof-carrying encoding with no code collection. -/
def encoding : _root_.Hypostructure.CT1.CertificateEncoding
    Previous PublicTarget where
  Code := fun previous =>
    {flag : Bool // flag = (Core.Residual.residualOf previous).enabled}
  Accepts := fun _previous code => code.1 = true
  encode := by
    intro previous target
    exact ⟨⟨true, target.symm⟩, rfl⟩
  decode := by
    intro previous code accepted
    exact code.2.symm.trans accepted
  acceptsDecidable := fun _previous code => Bool.decEq code.1 true

def hitResidual : Residual := ⟨true⟩

def hitPrevious : Previous := Core.Residual.Ledger.initial hitResidual

noncomputable def hitResult :=
  _root_.Hypostructure.CT1.executePublicTarget encoding hitPrevious

theorem hit_previous : hitResult.stage.previous = hitPrevious := rfl

theorem hit_target : PublicTarget hitPrevious := rfl

theorem hit_terminal : hitResult.terminal = .c1 := by
  apply hitResult.terminal_c1_of_target
  rw [hit_previous]
  exact hit_target

theorem hit_checks : hitResult.checks = 1 :=
  hitResult.checks_eq_one_of_c1 hit_terminal

theorem hit_trace :
    hitResult.traceNodes =
      [.entry, .publicTargetDecision, .certificateValidation, .c1Terminal] := by
  rw [hitResult.trace_exact, hit_terminal]
  rfl

theorem hit_decoded_target : PublicTarget hitPrevious := by
  have target : PublicTarget hitResult.stage.previous := by
    simpa [_root_.Hypostructure.CT1.CertificateEncoding.OutcomeClaim,
      hit_terminal] using hitResult.verified
  simpa [hit_previous] using target

theorem hit_work_exact :
    hitResult.checks =
      (_root_.Hypostructure.CT1.CertificateEncoding.successfulValidationBudget
        encoding).checks hitPrevious := by
  simpa [hit_previous] using
    hitResult.checks_eq_successfulBudget hit_terminal

def avoidingResidual : Residual := ⟨false⟩

def avoidingPrevious : Previous :=
  Core.Residual.Ledger.initial avoidingResidual

noncomputable def avoidingResult :=
  _root_.Hypostructure.CT1.executePublicTarget encoding avoidingPrevious

theorem avoiding_previous :
    avoidingResult.stage.previous = avoidingPrevious := rfl

theorem avoids_target : Not (PublicTarget avoidingPrevious) := by
  simp [PublicTarget, avoidingPrevious, avoidingResidual]

theorem avoiding_terminal : avoidingResult.terminal = .avoiding := by
  apply avoidingResult.terminal_avoiding_of_not_target
  rw [avoiding_previous]
  exact avoids_target

theorem avoiding_checks : avoidingResult.checks = 0 :=
  avoidingResult.checks_eq_zero_of_avoiding avoiding_terminal

theorem avoiding_trace :
    avoidingResult.traceNodes =
      [.entry, .publicTargetDecision, .avoidingTerminal] := by
  rw [avoidingResult.trace_exact, avoiding_terminal]
  rfl

theorem avoiding_verified : Not (PublicTarget avoidingPrevious) := by
  have avoids : Not (PublicTarget avoidingResult.stage.previous) := by
    simpa [_root_.Hypostructure.CT1.CertificateEncoding.OutcomeClaim,
      avoiding_terminal] using avoidingResult.verified
  simpa [avoiding_previous] using avoids

theorem avoiding_work_exact :
    avoidingResult.checks =
      (_root_.Hypostructure.CT1.CertificateEncoding.avoidingBudget
        encoding).checks avoidingPrevious := by
  simpa [avoiding_previous] using
    avoidingResult.checks_eq_avoidingBudget avoiding_terminal

/-- CT1, rather than the caller, closes the impossible C1 arm and retains the
literal decision stage as the predecessor of the surviving arm. -/
noncomputable def avoidingSuccessor :=
  _root_.Hypostructure.CT1.closeC1ContinueAvoiding encoding
    avoidingResult.stage (by
      rw [avoiding_previous]
      exact avoids_target)

theorem avoidingSuccessor_previous :
    avoidingSuccessor.previous = avoidingResult.stage :=
  rfl

theorem avoidingSuccessor_avoids :
    Not (PublicTarget avoidingSuccessor.previous.previous) :=
  avoidingSuccessor.added.avoids

theorem avoidingSuccessor_checks :
    avoidingSuccessor.previous.added.checks = 0 :=
  avoidingSuccessor.added.checks_eq_zero

theorem avoidingSuccessor_trace :
    (_root_.Hypostructure.CT1.CertificateEncoding.traceOfRoute
      avoidingSuccessor.previous.added).nodes =
      [.entry, .publicTargetDecision, .avoidingTerminal] := by
  exact avoidingSuccessor.added.trace_exact

end CertificateMode

namespace K4

abbrev Vertex := Fin 4

def graph : SimpleGraph Vertex := ⊤

def object : Graph.FiniteObject :=
  Graph.FiniteObject.of graph inferInstance (by
    change DecidableRel fun left right : Vertex => left ≠ right
    infer_instance)

/-- The literal closed walk `0-1-2-3-0`. -/
def fourCycle : graph.Walk (0 : Vertex) 0 :=
  .cons (v := 1) (by simp [graph])
    (.cons (v := 2) (by simp [graph])
      (.cons (v := 3) (by simp [graph])
        (.cons (v := 0) (by simp [graph]) .nil)))

def LengthOK (length : Nat) : Prop := length = 4

theorem fourCycle_isCycle : fourCycle.IsCycle := by
  rw [SimpleGraph.Walk.isCycle_def, SimpleGraph.Walk.isTrail_def]
  decide

def certificate : Graph.CycleCertificate object LengthOK := by
  dsimp only [object, Graph.FiniteObject.of]
  exact {
    vertex := 0
    walk := fourCycle
    isCycle := fourCycle_isCycle
    length_ok := rfl
  }

structure Residual (selected : Graph.FiniteObject) where
  candidates : Core.Finite.Enumeration
    (Graph.CycleCertificate selected LengthOK)
  card_le_one : candidates.card <= 1

abbrev Previous := Core.Residual.Ledger (Residual object)

def objectQuery : Core.Residual.Query Previous fun _previous =>
    Graph.FiniteObject :=
  (Core.Residual.Query.residual
    (Source := Previous) (Residual := Residual object)).map
      fun _previous _residual => object

def scheduleQuery : Core.Residual.Query Previous fun previous =>
    Core.Finite.Enumeration
      (Graph.CycleCertificate (objectQuery.read previous) LengthOK) :=
  (Core.Residual.Query.residual
    (Source := Previous) (Residual := Residual object)).map
    fun _current residual => by
      simpa [objectQuery] using residual.candidates

noncomputable def residual : Residual object where
  candidates := {
    values := [certificate]
    nodup := by simp
    decEq := Classical.decEq _
  }
  card_le_one := by decide

noncomputable def previous : Previous :=
  Core.Residual.Ledger.initial residual

def spec := Graph.CT1.cycleSpec objectQuery LengthOK

def capability := Graph.CT1.cycleCapability objectQuery LengthOK scheduleQuery
  (fun _previous => 0) 1 0 (by
    intro current
    change (Core.Residual.residualOf current).candidates.card <= 1
    exact (Core.Residual.residualOf current).card_le_one)

noncomputable def result :
    _root_.Hypostructure.CT1.ExecutionResult spec capability :=
  _root_.Hypostructure.CT1.execute spec capability previous

theorem result_previous : result.stage.previous = previous := rfl

theorem scheduled_target_explicit :
    _root_.Hypostructure.CT1.Target spec previous
      (capability.scheduleAt previous) := by
  refine ⟨certificate, ?_, trivial⟩
  change certificate ∈ [certificate]
  simp

theorem result_terminal : result.terminal = .c1 :=
  result.terminal_c1_of_target (by
    rw [result_previous]
    exact scheduled_target_explicit)

theorem result_checks : result.checks = 1 := by
  have positive : 0 < result.checks := result.checks_pos_of_c1 result_terminal
  have bounded := result.checks_le_polynomial
  have upper : result.checks <= 1 := by
    change result.checks <= 1 at bounded
    exact bounded
  omega

theorem result_trace :
    result.traceNodes =
      [.entry, .schedule, .realizationDecision, .c1Terminal] := by
  rw [result.trace_exact, result_terminal]
  rfl

theorem scheduled_target :
    _root_.Hypostructure.CT1.Target spec previous
      (capability.scheduleAt previous) :=
  scheduled_target_explicit

theorem public_cycle_target :
    Graph.HasCycleWithLength LengthOK object := by
  simpa [previous, residual, objectQuery] using
    Graph.CT1.publicTarget_of_target scheduled_target

def targetInterface :
    Graph.TargetInterface (Graph.HasCycleWithLength LengthOK) :=
  Graph.CT1.cycleInterface LengthOK

theorem result_work :
    result.checks <= capability.workCoefficient *
      (capability.inputSize previous + 1) ^ capability.workDegree :=
  result.checks_le_polynomial

end K4

namespace RootedReturnCertificate

def algebra : Graph.RootedReturnTargetAlgebra K4.LengthOK :=
  Graph.RootedReturnTargetAlgebra.shifted K4.LengthOK

def encoding :=
  Graph.CT1.rootedReturnEncoding K4.objectQuery K4.LengthOK algebra

noncomputable def hitResult :=
  Graph.CT1.executeRootedReturn K4.objectQuery K4.LengthOK algebra K4.previous

theorem hit_previous : hitResult.stage.previous = K4.previous := rfl

theorem hit_target :
    Graph.HasCycleWithLength K4.LengthOK
      (K4.objectQuery.read K4.previous) := by
  change Graph.HasCycleWithLength K4.LengthOK K4.object
  exact ⟨K4.certificate⟩

theorem hit_terminal : hitResult.terminal = .c1 := by
  apply hitResult.terminal_c1_of_target
  rw [hit_previous]
  exact hit_target

theorem hit_checks : hitResult.checks = 1 :=
  hitResult.checks_eq_one_of_c1 hit_terminal

theorem hit_work_exact :
    hitResult.checks =
      (_root_.Hypostructure.CT1.CertificateEncoding.successfulValidationBudget
        encoding).checks K4.previous := by
  simpa [hit_previous, encoding] using
    hitResult.checks_eq_successfulBudget hit_terminal

theorem hit_trace :
    hitResult.traceNodes =
      [.entry, .publicTargetDecision, .certificateValidation, .c1Terminal] := by
  rw [hitResult.trace_exact, hit_terminal]
  rfl

/-- The framework-selected rooted return decodes through the graph algebra to
the existing public cycle target. -/
theorem accepted_return_decodes :
    Graph.HasCycleWithLength K4.LengthOK
      (K4.objectQuery.read hitResult.stage.previous) :=
  encoding.decode (hitResult.acceptedCode hit_terminal).accepted

def NeverLength (_length : Nat) : Prop := False

def avoidingAlgebra : Graph.RootedReturnTargetAlgebra NeverLength :=
  Graph.RootedReturnTargetAlgebra.shifted NeverLength

def avoidingEncoding :=
  Graph.CT1.rootedReturnEncoding K4.objectQuery NeverLength avoidingAlgebra

noncomputable def avoidingResult :=
  Graph.CT1.executeRootedReturn K4.objectQuery NeverLength avoidingAlgebra
    K4.previous

theorem avoiding_previous :
    avoidingResult.stage.previous = K4.previous := rfl

theorem avoids_target :
    Not (Graph.HasCycleWithLength NeverLength
      (K4.objectQuery.read K4.previous)) := by
  rintro ⟨certificate⟩
  exact certificate.length_ok

theorem avoiding_terminal : avoidingResult.terminal = .avoiding := by
  apply avoidingResult.terminal_avoiding_of_not_target
  rw [avoiding_previous]
  exact avoids_target

theorem avoiding_checks : avoidingResult.checks = 0 :=
  avoidingResult.checks_eq_zero_of_avoiding avoiding_terminal

theorem avoiding_trace :
    avoidingResult.traceNodes =
      [.entry, .publicTargetDecision, .avoidingTerminal] := by
  rw [avoidingResult.trace_exact, avoiding_terminal]
  rfl

theorem avoiding_verified :
    Not (Graph.HasCycleWithLength NeverLength
      (K4.objectQuery.read K4.previous)) := by
  have avoids :
      Not (Graph.HasCycleWithLength NeverLength
        (K4.objectQuery.read avoidingResult.stage.previous)) := by
    simpa [_root_.Hypostructure.CT1.CertificateEncoding.OutcomeClaim,
      avoiding_terminal] using avoidingResult.verified
  simpa [avoiding_previous] using avoids

theorem avoiding_work_exact :
    avoidingResult.checks =
      (_root_.Hypostructure.CT1.CertificateEncoding.avoidingBudget
        avoidingEncoding).checks K4.previous := by
  simpa [avoiding_previous, avoidingEncoding] using
    avoidingResult.checks_eq_avoidingBudget avoiding_terminal

end RootedReturnCertificate

#print axioms Neutral.hit_previous
#print axioms Neutral.hit_terminal
#print axioms Neutral.hit_checks
#print axioms Neutral.hit_target
#print axioms Neutral.miss_previous
#print axioms Neutral.miss_terminal
#print axioms Neutral.miss_checks
#print axioms Neutral.miss_avoids
#print axioms CertificateMode.hit_terminal
#print axioms CertificateMode.hit_checks
#print axioms CertificateMode.hit_decoded_target
#print axioms CertificateMode.avoiding_terminal
#print axioms CertificateMode.avoiding_checks
#print axioms CertificateMode.avoiding_verified
#print axioms K4.fourCycle_isCycle
#print axioms K4.result_terminal
#print axioms K4.result_checks
#print axioms K4.public_cycle_target
#print axioms RootedReturnCertificate.hit_terminal
#print axioms RootedReturnCertificate.hit_checks
#print axioms RootedReturnCertificate.hit_work_exact
#print axioms RootedReturnCertificate.accepted_return_decodes
#print axioms RootedReturnCertificate.avoiding_terminal
#print axioms RootedReturnCertificate.avoiding_checks
#print axioms RootedReturnCertificate.avoiding_verified

end Hypostructure.Fixtures.CT1
