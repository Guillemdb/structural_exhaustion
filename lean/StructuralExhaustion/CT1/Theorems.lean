import StructuralExhaustion.CT1.Execution

namespace StructuralExhaustion.CT1

namespace RawOutcome

/-- Terminal evidence proves exactly its advertised semantic claim. -/
theorem verified {P : Core.Problem} {S : Spec P} {input : Input P}
    {terminal : Graph.Terminal} (outcome : RawOutcome S input terminal) :
    OutcomeClaim outcome := by
  cases outcome with
  | c1 certificate => exact certificate.target
  | avoiding state => exact state.targetAvoiding

end RawOutcome

namespace ExecutionResult

theorem verified {P : Core.Problem} {S : Spec P} {input : Input P}
    (result : ExecutionResult S input) : OutcomeClaim result.outcome :=
  result.outcome.verified

theorem traceValid {P : Core.Problem} {S : Spec P} {input : Input P}
    (result : ExecutionResult S input) :
    @Graph.ValidTrace P S input result.trace :=
  ⟨result.terminal, result.path, rfl⟩

end ExecutionResult

namespace TargetBridge

/-- Interpret a public target through its bridge to CT1's canonical target. -/
theorem target_of_publicTarget
    {P : Core.Problem} {S : Spec P} {PublicTarget : P.Ambient → Prop}
    (bridge : TargetBridge S PublicTarget) {G : P.Ambient}
    (publicTarget : PublicTarget G) : Target S G :=
  (bridge.equivalent G).mp publicTarget

/-- Export CT1's canonical target as the problem's public target. -/
theorem publicTarget_of_target
    {P : Core.Problem} {S : Spec P} {PublicTarget : P.Ambient → Prop}
    (bridge : TargetBridge S PublicTarget) {G : P.Ambient}
    (target : Target S G) : PublicTarget G :=
  (bridge.equivalent G).mpr target

/-- A framework-produced C1 certificate closes the bridged public target. -/
theorem publicTarget_of_c1
    {P : Core.Problem} {S : Spec P} {PublicTarget : P.Ambient → Prop}
    (bridge : TargetBridge S PublicTarget) {input : Input P}
    {equivalence : EquivalenceState S input}
    (certificate : C1Certificate S input equivalence) :
    PublicTarget input.context.G :=
  publicTarget_of_target bridge certificate.target

/-- Canonical target avoidance excludes the bridged public target. -/
theorem not_publicTarget_of_not_target
    {P : Core.Problem} {S : Spec P} {PublicTarget : P.Ambient → Prop}
    (bridge : TargetBridge S PublicTarget) {G : P.Ambient}
    (notTarget : ¬ Target S G) : ¬ PublicTarget G :=
  fun publicTarget => notTarget (target_of_publicTarget bridge publicTarget)

/-- A framework-produced avoiding state excludes the bridged public target. -/
theorem not_publicTarget_of_avoiding
    {P : Core.Problem} {S : Spec P} {PublicTarget : P.Ambient → Prop}
    (bridge : TargetBridge S PublicTarget) {input : Input P}
    {equivalence : EquivalenceState S input}
    (state : AvoidingState S input equivalence) :
    ¬ PublicTarget input.context.G :=
  not_publicTarget_of_not_target bridge state.targetAvoiding

/-- Transport monotonicity of a public target through two canonical CT1
bridges.  This is the standard adapter needed when a reduction changes the
ambient object but preserves the public mathematical target. -/
theorem target_mono_of_publicTarget_mono
    {P : Core.Problem} {S : Spec P} {PublicTarget : P.Ambient → Prop}
    (bridge : TargetBridge S PublicTarget) {smaller larger : P.Ambient}
    (publicMono : PublicTarget smaller → PublicTarget larger)
    (target : Target S smaller) : Target S larger :=
  target_of_publicTarget bridge
    (publicMono (publicTarget_of_target bridge target))

/-- Decide a bridged public target using CT1's exhaustive finite search. -/
def publicTargetDecidable
    {P : Core.Problem} {S : Spec P} {PublicTarget : P.Ambient → Prop}
    (bridge : TargetBridge S PublicTarget) (capability : Capability S)
    (G : P.Ambient) : Decidable (PublicTarget G) := by
  letI : Decidable (Target S G) := targetDecidable S capability G
  exact decidable_of_iff (Target S G) (bridge.equivalent G).symm

end TargetBridge

/-- Aggregate semantic soundness of the framework-generated CT1 run. -/
theorem run_verified {P : Core.Problem} (S : Spec P)
    (capability : Capability S)
    (input : Input P) : OutcomeClaim (run S capability input).outcome :=
  (run S capability input).verified

/-- The erased trace of every run is backed by its exact dependent path. -/
theorem run_trace_valid {P : Core.Problem} (S : Spec P)
    (capability : Capability S)
    (input : Input P) :
    @Graph.ValidTrace P S input (run S capability input).trace :=
  (run S capability input).traceValid

/-- CT1 is total from the finite executable capability alone. -/
theorem run_total {P : Core.Problem} (S : Spec P)
    (capability : Capability S)
    (input : Input P) :
    ∃ result : ExecutionResult S input,
      OutcomeClaim result.outcome ∧
        @Graph.ValidTrace P S input result.trace := by
  let result := run S capability input
  exact ⟨result, result.verified, result.traceValid⟩

/-- Reference execution is a function and hence deterministic.  This theorem
states the useful relational form consumed by schedulers and audit tooling. -/
theorem run_deterministic {P : Core.Problem} (S : Spec P)
    (capability : Capability S)
    (input : Input P) (first second : ExecutionResult S input)
    (hFirst : run S capability input = first)
    (hSecond : run S capability input = second) : first = second :=
  hFirst.symm.trans hSecond

theorem outcome_exhaustive {P : Core.Problem} {S : Spec P}
    {input : Input P} (result : ExecutionResult S input) :
    result.terminal = .c1 ∨ result.terminal = .avoiding := by
  cases result with
  | mk _ _ outcome =>
      cases outcome with
      | c1 _ => exact Or.inl rfl
      | avoiding _ => exact Or.inr rfl

/-! ## Certificate-driven local execution -/

/-- A successful CT1 execution constructed directly from one realized local
witness.  It follows the ordinary typed C1 path but performs no search over a
witness universe. -/
def executionOfRealization {P : Core.Problem} (S : Spec P)
    (input : Input P) (index : S.TestIndex)
    (witness : S.Witness input.context.G index)
    (realizes : S.Realizes input.context.G index witness) :
    ExecutionResult S input :=
  let equivalence := certifyEquivalence S input
  let certificate : C1Certificate S input equivalence :=
    ⟨index, witness, realizes⟩
  {
    terminal := .c1
    path := .cons .beginEquivalence
      (.cons (.equivalenceCertified equivalence)
        (.cons (.realizationHit certificate) (.nil .c1Terminal)))
    outcome := .c1 certificate
  }

/-- Audited local C1 run.  One primitive check denotes validation of the
supplied realization certificate; no candidate enumeration is performed. -/
structure CertifiedC1Run {P : Core.Problem} (S : Spec P)
    (input : Input P) where
  result : ExecutionResult S input
  checks : Nat
  terminal_eq : result.terminal = .c1
  trace_eq : result.trace =
    [.entry, .equivalenceCertification, .realizationDecision, .c1Terminal]
  checks_eq : checks = 1

/-- Construct the local C1 run from an explicit realization. -/
def runC1OfRealization {P : Core.Problem} (S : Spec P)
    (input : Input P) (index : S.TestIndex)
    (witness : S.Witness input.context.G index)
    (realizes : S.Realizes input.context.G index witness) :
    CertifiedC1Run S input where
  result := executionOfRealization S input index witness realizes
  checks := 1
  terminal_eq := rfl
  trace_eq := rfl
  checks_eq := rfl

theorem certifiedC1Run_verified {P : Core.Problem} {S : Spec P}
    {input : Input P} (result : CertifiedC1Run S input) :
    OutcomeClaim result.result.outcome :=
  result.result.verified

theorem certifiedC1Run_checks_le {P : Core.Problem} {S : Spec P}
    {input : Input P} (result : CertifiedC1Run S input) :
    result.checks ≤ 1 := by
  simp [result.checks_eq]

/-- Certificate-driven CT1 has a uniform degree-zero work budget. -/
def certifiedC1Budget {P : Core.Problem} (_S : Spec P) :
    Core.PolynomialCheckBudget (Input P) :=
  Core.PolynomialCheckBudget.constant (fun _ => 1) 1

/-- If CT1's canonical target already holds, completeness of the exact finite
search forces the reference runner to terminate at C1. -/
theorem run_terminal_c1_of_target {P : Core.Problem} (S : Spec P)
    (capability : Capability S) (input : Input P)
    (target : Target S input.context.G) :
    (run S capability input).terminal = .c1 := by
  cases decision : findRealization S capability input
      (certifyEquivalence S input) with
  | hit certificate =>
      simp [run, runReference, decision]
  | avoiding state =>
      exact (state.targetAvoiding target).elim

/-- A bridged public target is enough to force the actual CT1 runner to C1. -/
theorem run_terminal_c1_of_publicTarget {P : Core.Problem} (S : Spec P)
    (capability : Capability S) {PublicTarget : P.Ambient → Prop}
    (bridge : TargetBridge S PublicTarget) (input : Input P)
    (target : PublicTarget input.context.G) :
    (run S capability input).terminal = .c1 :=
  run_terminal_c1_of_target S capability input
    (bridge.target_of_publicTarget target)

private theorem trace_to_c1 {P : Core.Problem} {S : Spec P}
    {input : Input P}
    (path : Graph.Path S input .entry .c1Terminal) :
    path.trace =
      [.entry, .equivalenceCertification, .realizationDecision,
        .c1Terminal] := by
  cases path with
  | cons first remaining =>
      cases first with
      | beginEquivalence =>
          cases remaining with
          | cons second remaining =>
              cases second with
              | equivalenceCertified equivalence =>
                  cases remaining with
                  | cons third remaining =>
                      cases third with
                      | realizationHit certificate =>
                          cases remaining with
                          | nil => rfl
                          | cons edge tail => cases edge
                      | realizationAvoiding state =>
                          cases remaining with
                          | cons edge tail => cases edge

/-- Under the same canonical target premise, CT1's complete reference audit
trace is the C1 path.  Applications need not repeat the search case split to
expose this trace. -/
theorem run_trace_c1_of_target {P : Core.Problem} (S : Spec P)
    (capability : Capability S) (input : Input P)
    (target : Target S input.context.G) :
    (run S capability input).trace =
      [.entry, .equivalenceCertification, .realizationDecision,
        .c1Terminal] := by
  let result := run S capability input
  change result.trace = _
  rcases result with ⟨terminal, path, outcome⟩
  cases outcome with
  | c1 certificate =>
      exact trace_to_c1 path
  | avoiding state =>
      exact (state.targetAvoiding target).elim

/-- A bridged public target determines the exact successful CT1 trace. -/
theorem run_trace_c1_of_publicTarget {P : Core.Problem} (S : Spec P)
    (capability : Capability S) {PublicTarget : P.Ambient → Prop}
    (bridge : TargetBridge S PublicTarget) (input : Input P)
    (target : PublicTarget input.context.G) :
    (run S capability input).trace =
      [.entry, .equivalenceCertification, .realizationDecision,
        .c1Terminal] :=
  run_trace_c1_of_target S capability input
    (bridge.target_of_publicTarget target)

/-- Exact successful execution bundle.  It identifies the exposed result with
the reference runner and packages both the forced terminal and its full trace. -/
structure C1Run {P : Core.Problem} (S : Spec P)
    (capability : Capability S) (input : Input P) where
  result : ExecutionResult S input
  result_eq : result = run S capability input
  terminal_eq : result.terminal = .c1
  trace_eq : result.trace =
    [.entry, .equivalenceCertification, .realizationDecision, .c1Terminal]

/-- Build the exact successful execution bundle from a canonical target. -/
def runC1OfTarget {P : Core.Problem} (S : Spec P)
    (capability : Capability S) (input : Input P)
    (target : Target S input.context.G) : C1Run S capability input where
  result := run S capability input
  result_eq := rfl
  terminal_eq := run_terminal_c1_of_target S capability input target
  trace_eq := run_trace_c1_of_target S capability input target

/-- Build the exact successful execution bundle directly from a public
mathematical target and its reusable bridge. -/
def runC1OfPublicTarget {P : Core.Problem} (S : Spec P)
    (capability : Capability S) {PublicTarget : P.Ambient → Prop}
    (bridge : TargetBridge S PublicTarget) (input : Input P)
    (target : PublicTarget input.context.G) : C1Run S capability input :=
  runC1OfTarget S capability input (bridge.target_of_publicTarget target)

theorem c1_terminal_closes {P : Core.Problem} {S : Spec P}
    {input : Input P} {equivalence : EquivalenceState S input}
    (certificate : C1Certificate S input equivalence) :
    Target S input.context.G :=
  certificate.target

theorem avoiding_terminal_excludes_target {P : Core.Problem} {S : Spec P}
    {input : Input P} {equivalence : EquivalenceState S input}
    (state : AvoidingState S input equivalence) :
    ¬ Target S input.context.G :=
  state.targetAvoiding

end StructuralExhaustion.CT1
