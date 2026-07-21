import Hypostructure.CT4.Theorems

/-!
# CT4 functional-cardinality profile

This profile captures the common case in which one payer cannot serve two
different demands.  A strict cardinality gap then forces the framework's
canonical missing-payer terminal.  The proof counts only the two exact
residual-owned schedules.
-/

namespace Hypostructure.CT4

universe uPrevious uDemand uPayer

/-- Minimal profile for first-unused-resource arguments. -/
structure FunctionalCardinalityProfile (Previous : Type uPrevious) where
  Demand : Previous -> Type uDemand
  Payer : Previous -> Type uPayer
  Eligible : (previous : Previous) -> Demand previous -> Payer previous -> Prop
  demands : Core.Residual.Query Previous fun previous =>
    Core.Finite.Enumeration (Demand previous)
  payers : Core.Residual.Query Previous fun previous =>
    Core.Finite.Enumeration (Payer previous)
  eligibleDecidable : (previous : Previous) -> (demand : Demand previous) ->
    (payer : Payer previous) -> Decidable (Eligible previous demand payer)
  functional : forall previous payer demandLeft demandRight,
    Eligible previous demandLeft payer ->
      Eligible previous demandRight payer -> demandLeft = demandRight
  inputSize : Previous -> Nat
  workCoefficient : Nat
  workDegree : Nat
  workBound : forall previous,
    localCheckBound (demands.read previous) (payers.read previous) <=
      workCoefficient * (inputSize previous + 1) ^ workDegree

namespace FunctionalCardinalityProfile

/-- CT4 semantics generated from the functional profile. -/
def spec (profile : FunctionalCardinalityProfile.{uPrevious, uDemand, uPayer}
    Previous) : Spec Previous where
  Demand := profile.Demand
  Payer := profile.Payer
  Eligible := profile.Eligible
  demandWeight := fun _previous _demand => 0
  capacity := fun _previous _payer => 0
  required := fun _previous => 0

/-- Executable CT4 capability generated from the functional profile. -/
def capability
    (profile : FunctionalCardinalityProfile.{uPrevious, uDemand, uPayer}
      Previous) : Capability profile.spec where
  demands := profile.demands
  payers := profile.payers
  eligibleDecidable := profile.eligibleDecidable
  inputSize := profile.inputSize
  workCoefficient := profile.workCoefficient
  workDegree := profile.workDegree
  workBound := profile.workBound

/-- Exact CT4 run generated from the profile. -/
def run (profile : FunctionalCardinalityProfile.{uPrevious, uDemand, uPayer}
    Previous) (previous : Previous) :
    ExecutionResult profile.spec profile.capability :=
  CT4.run profile.spec profile.capability previous

end FunctionalCardinalityProfile

variable {spec : Spec.{uPrevious, uDemand, uPayer} Previous}

/-- Exact payer-schedule index selected for one demand-schedule index. -/
def assignedIndex {capability : Capability spec} {previous : Previous}
    (total : TotalAssignmentState capability previous)
    (index : Fin (capability.demandsAt previous).card) :
    Fin (capability.payersAt previous).card :=
  ((total.assignment.execution
      ((capability.demandsAt previous).get index)).hitOfHasHit
    (total.total ((capability.demandsAt previous).get index)
      ((capability.demandsAt previous).get_mem index))).index

/-- Functional eligibility makes the canonical scheduled assignment
injective on demand indices. -/
theorem assignedIndex_injective {capability : Capability spec}
    {previous : Previous}
    (total : TotalAssignmentState capability previous)
    (functional : forall payer demandLeft demandRight,
      spec.Eligible previous demandLeft payer ->
        spec.Eligible previous demandRight payer ->
          demandLeft = demandRight) :
    Function.Injective (assignedIndex total) := by
  intro left right equalIndex
  let leftHit := (total.assignment.execution
      ((capability.demandsAt previous).get left)).hitOfHasHit
    (total.total ((capability.demandsAt previous).get left)
      ((capability.demandsAt previous).get_mem left))
  let rightHit := (total.assignment.execution
      ((capability.demandsAt previous).get right)).hitOfHasHit
    (total.total ((capability.demandsAt previous).get right)
      ((capability.demandsAt previous).get_mem right))
  have payerIndexEqual : leftHit.index = rightHit.index := by
    exact equalIndex
  have payerEqual : leftHit.value = rightHit.value := by
    exact congrArg (capability.payersAt previous).get payerIndexEqual
  have demandEqual : (capability.demandsAt previous).get left =
      (capability.demandsAt previous).get right :=
    functional leftHit.value
      ((capability.demandsAt previous).get left)
      ((capability.demandsAt previous).get right)
      leftHit.sound (payerEqual ▸ rightHit.sound)
  exact (capability.demandsAt previous).unique_index demandEqual

/-- Any total functional assignment injects the exact demand schedule into
the exact payer schedule. -/
theorem card_demands_le_card_payers_of_total
    {capability : Capability spec} {previous : Previous}
    (total : TotalAssignmentState capability previous)
    (functional : forall payer demandLeft demandRight,
      spec.Eligible previous demandLeft payer ->
        spec.Eligible previous demandRight payer ->
          demandLeft = demandRight) :
    (capability.demandsAt previous).card <=
      (capability.payersAt previous).card := by
  have finiteBound := Fintype.card_le_of_injective (assignedIndex total)
    (assignedIndex_injective total functional)
  simpa only [Fintype.card_fin] using finiteBound

/-- Strictly fewer functional payers force any generated terminal-indexed
outcome to be the missing-payer branch. -/
theorem Outcome.terminal_eq_missing_of_card_lt
    {capability : Capability spec} {previous : Previous} {terminal : Terminal}
    (outcome : Outcome capability previous terminal)
    (functional : forall payer demandLeft demandRight,
      spec.Eligible previous demandLeft payer ->
        spec.Eligible previous demandRight payer ->
          demandLeft = demandRight)
    (cardLt : (capability.payersAt previous).card <
      (capability.demandsAt previous).card) :
    terminal = .missingPayer := by
  cases outcome with
  | missingPayer _assignment _residual => rfl
  | overloadedFibre total _residual =>
      exact (Nat.not_le_of_gt cardLt
        (card_demands_le_card_payers_of_total total functional)).elim
  | c4 total _bounded _certificate =>
      exact (Nat.not_le_of_gt cardLt
        (card_demands_le_card_payers_of_total total functional)).elim
  | capacity total _bounded _residual =>
      exact (Nat.not_le_of_gt cardLt
        (card_demands_le_card_payers_of_total total functional)).elim

/-- Strictly fewer functional payers force any generated CT4 result to the
missing-payer terminal. -/
theorem ExecutionResult.terminal_eq_missing_of_card_lt
    {capability : Capability spec}
    (result : ExecutionResult spec capability)
    (functional : forall payer demandLeft demandRight,
      spec.Eligible result.stage.previous demandLeft payer ->
        spec.Eligible result.stage.previous demandRight payer ->
          demandLeft = demandRight)
    (cardLt : (capability.payersAt result.stage.previous).card <
      (capability.demandsAt result.stage.previous).card) :
    result.terminal = .missingPayer :=
  result.outcome.terminal_eq_missing_of_card_lt functional cardLt

/-- Framework projection of a missing terminal into its schedule-level
semantic certificate. -/
structure MissingCertificate (capability : Capability spec)
    (previous : Previous) where
  private mk ::
  demand : spec.Demand previous
  scheduled : demand ∈ (capability.demandsAt previous).values
  noEligible : forall payer,
    payer ∈ (capability.payersAt previous).values ->
      Not (spec.Eligible previous demand payer)

/-- Recover the canonical missing-demand semantics from terminal-indexed
framework evidence. -/
def Outcome.missingCertificate {capability : Capability spec}
    {previous : Previous} {terminal : Terminal}
    (outcome : Outcome capability previous terminal)
    (isMissing : terminal = .missingPayer) :
    MissingCertificate capability previous := by
  cases outcome with
  | missingPayer _assignment residual =>
      exact .mk residual.demand residual.scheduled residual.noEligible
  | overloadedFibre _total _residual => cases isMissing
  | c4 _total _bounded _certificate => cases isMissing
  | capacity _total _bounded _residual => cases isMissing

/-- Recover missing semantics from a completed execution. -/
def ExecutionResult.missingCertificate {capability : Capability spec}
    (result : ExecutionResult spec capability)
    (isMissing : result.terminal = .missingPayer) :
    MissingCertificate capability result.stage.previous :=
  result.outcome.missingCertificate isMissing

namespace FunctionalCardinalityProfile

/-- A strict schedule-cardinality gap forces the generated profile run to the
missing terminal. -/
theorem run_terminal_eq_missing
    (profile : FunctionalCardinalityProfile.{uPrevious, uDemand, uPayer}
      Previous) (previous : Previous)
    (cardLt : (profile.payers.read previous).card <
      (profile.demands.read previous).card) :
    (profile.run previous).terminal = .missingPayer := by
  apply ExecutionResult.terminal_eq_missing_of_card_lt
  · exact profile.functional previous
  · exact cardLt

/-- Canonical missing-demand semantics generated by a strict functional
cardinality gap. -/
def missingCertificate
    (profile : FunctionalCardinalityProfile.{uPrevious, uDemand, uPayer}
      Previous) (previous : Previous)
    (cardLt : (profile.payers.read previous).card <
      (profile.demands.read previous).card) :
    MissingCertificate profile.capability previous :=
  (profile.run previous).missingCertificate
    (profile.run_terminal_eq_missing previous cardLt)

end FunctionalCardinalityProfile

end Hypostructure.CT4
