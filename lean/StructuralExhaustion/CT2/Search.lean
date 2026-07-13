import StructuralExhaustion.CT2.State

namespace StructuralExhaustion.CT2

universe uAmbient uBranch uPiece uInterface uAbstract uContext uCandidate

variable {P : Core.Problem.{uAmbient, uBranch}}
variable {Target : P.Ambient → Prop}
variable (capability : Capability.{uAmbient, uBranch, uPiece, uInterface,
  uAbstract, uContext, uCandidate} P Target)
variable (ctx : Core.MinimalCounterexampleContext P Target)
variable (input : Input capability ctx)

/-! Generic exhaustive algorithms implementing CT2's mathematical nodes. -/

inductive DeletionDecision where
  | closes (witness : DeletionWitness capability ctx input)
  | critical (state : DeletionCriticalState capability ctx input)

/-- Decide the smaller-deletion counterexample directly from baseline and
target observations. -/
def analyzeDeletion : DeletionDecision capability ctx input :=
  let deleted := capability.reductions.delete input.seed.piece
  match capability.observable.baselineDecidable deleted.value with
  | .isFalse baselineAbsent =>
      .critical ⟨fun counterexample => baselineAbsent counterexample.1⟩
  | .isTrue baseline =>
      match capability.observable.targetDecidable deleted.value with
      | .isFalse avoids =>
          .closes ⟨baseline, avoids⟩
      | .isTrue target =>
          .critical ⟨fun counterexample => counterexample.2 target⟩

inductive CandidateContextDecision
    (candidate : capability.replacements.Candidate input.seed.piece) where
  | equivalent (proof : ContextEquivalent capability ctx input candidate)
  | separating (separator : ContextSeparator capability ctx input candidate)

/-- Exhaustively compare a candidate with the source in every exact context. -/
def analyzeCandidate
    (candidate : capability.replacements.Candidate input.seed.piece) :
    CandidateContextDecision capability ctx input candidate :=
  let contexts := capability.contexts.contexts
    (capability.interfaces.interface input.seed.piece)
  match Core.FiniteSearch.search contexts
      (fun context => sourceObservation capability ctx input context ≠
        replacementObservation capability ctx input candidate context)
      (fun _ => inferInstance) with
  | .found context differs => .separating ⟨context, differs⟩
  | .absent noDifference => .equivalent fun context =>
      match decEq (sourceObservation capability ctx input context)
        (replacementObservation capability ctx input candidate context) with
      | .isTrue same => same
      | .isFalse differs => (noDifference context differs).elim

/-- Exact context equivalence is decidable by the reference comparison. -/
def contextEquivalentDecidable
    (candidate : capability.replacements.Candidate input.seed.piece) :
    Decidable (ContextEquivalent capability ctx input candidate) :=
  match analyzeCandidate capability ctx input candidate with
  | .equivalent proof => .isTrue proof
  | .separating separator => .isFalse separator.notEquivalent

/-- Turn exhaustive absence of an equivalent candidate into a complete table
of concrete separating contexts. -/
def replacementTable
    (noEquivalent : ∀ candidate : capability.replacements.Candidate input.seed.piece,
      ¬ ContextEquivalent capability ctx input candidate) :
    ReplacementTable capability ctx input where
  separator := fun candidate =>
    match analyzeCandidate capability ctx input candidate with
    | .equivalent proof => (noEquivalent candidate proof).elim
    | .separating separator => separator

inductive ReplacementDecision where
  | closes (witness : ReplacementWitness capability ctx input)
  | separating (residual : SeparatingContextResidual capability ctx input)
  | critical (residual : CriticalityResidual capability ctx input)

/-- Search every legal candidate for an exact equivalent.  Only after proving
that no candidate is equivalent does the runner expose a separating residual
or, for an empty candidate universe, a criticality residual. -/
def analyzeReplacements
    (deletionCritical : DeletionCriticalState capability ctx input) :
    ReplacementDecision capability ctx input :=
  let candidates := capability.replacements.candidates input.seed.piece
  match Core.FiniteSearch.search candidates
      (ContextEquivalent capability ctx input)
      (contextEquivalentDecidable capability ctx input) with
  | .found candidate equivalent =>
      let current := capability.contexts.currentContext input.seed.piece
      let same := equivalent current
      have sourceBaseline : P.Baseline
          (sourceObject capability ctx input current) := by
        rw [sourceObject_current]
        exact ctx.baseline
      have sourceAvoids : ¬ Target
          (sourceObject capability ctx input current) := by
        rw [sourceObject_current]
        exact ctx.avoids
      have replacementBaseline : P.Baseline
          (replacementObject capability ctx input candidate current) :=
        capability.observable.baseline_of_observation_eq same sourceBaseline
      have replacementAvoids : ¬ Target
          (replacementObject capability ctx input candidate current) :=
        capability.observable.avoids_of_observation_eq same sourceAvoids
      .closes {
        candidate := candidate
        equivalent := equivalent
        baseline := replacementBaseline
        avoids := replacementAvoids
      }
  | .absent noEquivalent =>
      let table := replacementTable capability ctx input noEquivalent
      match elemsEq : candidates.orderedValues with
      | [] => .critical {
          deletionCritical := deletionCritical
          replacementTable := table
          noCandidate := fun candidate => by
            have member := candidates.mem_orderedValues candidate
            rw [elemsEq] at member
            cases member
        }
      | candidate :: _ => .separating {
          deletionCritical := deletionCritical
          candidate := candidate
          separator := table.separator candidate
          replacementTable := table
        }

theorem analyzeCandidate_sound
    (candidate : capability.replacements.Candidate input.seed.piece) :
    match analyzeCandidate capability ctx input candidate with
    | .equivalent _ => ContextEquivalent capability ctx input candidate
    | .separating _ =>
        ¬ ContextEquivalent capability ctx input candidate := by
  cases analyzeCandidate capability ctx input candidate with
  | equivalent proof => exact proof
  | separating separator => exact separator.notEquivalent

theorem replacementTable_complete
    (noEquivalent : ∀ candidate : capability.replacements.Candidate input.seed.piece,
      ¬ ContextEquivalent capability ctx input candidate) :
    ∀ candidate, ¬ ContextEquivalent capability ctx input candidate :=
  (replacementTable capability ctx input noEquivalent).noEquivalent

/-- Replacement search cannot emit a residual when any exact equivalent
candidate exists, even if earlier candidates in enumeration order separate. -/
theorem analyzeReplacements_closes_of_equivalent
    (deletionCritical : DeletionCriticalState capability ctx input)
    (existsEquivalent : ∃ candidate, ContextEquivalent capability ctx input candidate) :
    ∃ witness : ReplacementWitness capability ctx input,
      analyzeReplacements capability ctx input deletionCritical = .closes witness := by
  cases resultEq : analyzeReplacements capability ctx input deletionCritical with
  | closes witness => exact ⟨witness, rfl⟩
  | separating residual =>
      obtain ⟨candidate, equivalent⟩ := existsEquivalent
      exact (ReplacementTable.noEquivalent capability ctx input
        residual.replacementTable candidate equivalent).elim
  | critical residual =>
      obtain ⟨candidate, equivalent⟩ := existsEquivalent
      exact (ReplacementTable.noEquivalent capability ctx input
        residual.replacementTable candidate equivalent).elim

/-- If the exact candidate type is empty, replacement analysis reaches the
criticality residual rather than treating search failure as an unproved fact. -/
theorem analyzeReplacements_critical_of_no_candidate
    (deletionCritical : DeletionCriticalState capability ctx input)
    (noCandidate : ∀ _candidate :
      capability.replacements.Candidate input.seed.piece, False) :
    ∃ residual : CriticalityResidual capability ctx input,
      analyzeReplacements capability ctx input deletionCritical = .critical residual := by
  cases resultEq : analyzeReplacements capability ctx input deletionCritical with
  | closes witness => exact (noCandidate witness.candidate).elim
  | separating residual => exact (noCandidate residual.candidate).elim
  | critical residual => exact ⟨residual, rfl⟩

/-- Both deletion branches carry their exact mathematical dichotomy. -/
theorem analyzeDeletion_sound :
    match analyzeDeletion capability ctx input with
    | .closes _ =>
        P.Baseline (capability.reductions.delete input.seed.piece).value ∧
        ¬ Target (capability.reductions.delete input.seed.piece).value
    | .critical _ =>
        ¬ (P.Baseline (capability.reductions.delete input.seed.piece).value ∧
          ¬ Target (capability.reductions.delete input.seed.piece).value) := by
  cases analyzeDeletion capability ctx input with
  | closes witness => exact ⟨witness.baseline, witness.avoids⟩
  | critical state => exact state.notCounterexample

end StructuralExhaustion.CT2
