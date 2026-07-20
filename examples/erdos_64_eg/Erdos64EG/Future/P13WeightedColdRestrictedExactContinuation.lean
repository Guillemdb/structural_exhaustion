import Erdos64EG.Future.P13WeightedColdRestrictedF5Germ

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

variable {ctx : Core.MinimalCounterexampleContext
  PackedProblem.{u} PackedTarget.{u}}
variable {node21 : VerifiedP13MultiScaleCurvaturePrefix ctx}

namespace P13WeightedColdRestrictedPrefixPackage

set_option maxHeartbeats 800000
set_option maxRecDepth 10000

variable (package : P13WeightedColdRestrictedPrefixPackage ctx node21)
variable {ledger : package.PriorD6Ledger}
variable (survivor : package.LocalCorridorSurvivor ledger)

/-!
# Exact graph-owned F2--F5 semantics at original node [153]

This is the missing composition of the already constructed local producers.
At one stored prefix, F2 and F3 inspect only literal earlier prefixes with the
same complete structural state.  F2 chooses one distinguishing context from a
negated universal statement; it never enumerates contexts.  F4 scans the
inherited finite produced-support ledger.  If every stage is clear, the same
structural corridor run supplies the terminal or repeated F5 support.
-/

/-- One literal F2 occurrence at the current stage. -/
structure StageF2 (stage : package.Stage) where
  prior : package.Stage
  pair : package.MatchedPriorPiecePair survivor stage prior
  distinction : pair.F2Distinction

/-- One literal F3 occurrence, including the proper representative required
by the manuscript. -/
structure StageF3 (stage : package.Stage) where
  prior : package.Stage
  pair : package.MatchedPriorPiecePair survivor stage prior
  universal : pair.UniversalTargetEquality
  proposal : pair.ProperRepresentativeProposal

abbrev F2At (stage : package.Stage) : Prop :=
  Nonempty (package.StageF2 survivor stage)

abbrev F3At (stage : package.Stage) : Prop :=
  Nonempty (package.StageF3 survivor stage)

abbrev F4At (stage : package.Stage) : Prop :=
  Nonempty (package.D6F4Hit ledger stage)

/-- Uniform payload retained by the generic first-failure runner. -/
abbrev F2Data := Sigma fun stage => package.StageF2 survivor stage
abbrev F3Data := Sigma fun stage => package.StageF3 survivor stage
abbrev F4Data := Sigma fun stage => package.D6F4Hit ledger stage

/-- The exhaustive F5 output on the existing final alternative of node [153]. -/
inductive ExactF5
  | terminal (f1Clear : package.F1Clear)
      (short : (package.coldStructuralCorridorProfile survivor).stages.values.length ≤
        (package.coldStructuralCorridorProfile survivor).stateBound)
      (support : package.TerminalF5Support survivor f1Clear short)
  | repeated (f1Clear : package.F1Clear)
      (repetition : (package.coldStructuralCorridorProfile survivor).Repeated)
      (universal :
        (package.repeatedMatchedPriorPiecePair survivor repetition).UniversalTargetEquality)
      (negative :
        (package.repeatedMatchedPriorPiecePair survivor repetition).F3Negative)
      (support : package.RepeatedF5Support survivor f1Clear repetition
        universal negative)

/-- The generic adapter passes the inspected schedule abstractly.  Retaining
it here makes the equality with this package's literal stage list explicit
instead of assuming it inside the generic Core contract. -/
structure ScheduledF5 where
  schedule : List package.Stage
  ofExactSchedule : schedule = package.stages.values →
    package.ExactF5 survivor

noncomputable def f2Decidable (stage : package.Stage) :
    Decidable (package.F2At survivor stage) := Classical.dec _

noncomputable def f3Decidable (stage : package.Stage) :
    Decidable (package.F3At survivor stage) := Classical.dec _

noncomputable def f4Decidable (stage : package.Stage) :
    Decidable (package.F4At (ledger := ledger) stage) := Classical.dec _

noncomputable def f2Data (stage : package.Stage)
    (hit : package.F2At survivor stage) : package.F2Data survivor :=
  ⟨stage, Classical.choice hit⟩

noncomputable def f3Data (stage : package.Stage)
    (hit : package.F3At survivor stage) : package.F3Data survivor :=
  ⟨stage, Classical.choice hit⟩

noncomputable def f4Data (stage : package.Stage)
    (hit : package.F4At (ledger := ledger) stage) :
    package.F4Data (ledger := ledger) :=
  ⟨stage, Classical.choice hit⟩

theorem f4_absent (survivor : package.LocalCorridorSurvivor ledger)
    (stage : package.Stage) :
    ¬package.F4At (ledger := ledger) stage := by
  rintro ⟨hit⟩
  have outside := (survivor.clear stage).priorComplete.endpointOutside
    hit.hit.first.value
  apply outside
  rw [← hit.eventExact]
  exact hit.endpointMem

theorem everyStage_mem (stage : package.Stage) :
    stage ∈ package.stages.values := by
  change stage ∈ package.profile.stages.values
  rw [package.profile.stages_values_eq_finRange]
  exact List.mem_finRange stage

/-- A repeated structural pair with an F2 distinction is exactly an F2 event
at its later occurrence. -/
noncomputable def repeatedStageF2
    (repetition : (package.coldStructuralCorridorProfile survivor).Repeated)
    (distinction :
      (package.repeatedMatchedPriorPiecePair survivor repetition).F2Distinction) :
    package.StageF2 survivor repetition.second :=
  ⟨repetition.first,
    package.repeatedMatchedPriorPiecePair survivor repetition,
    distinction⟩

/-- A repeated pair with universal response and a proper representative is
exactly an F3 event at its later occurrence. -/
noncomputable def repeatedStageF3
    (repetition : (package.coldStructuralCorridorProfile survivor).Repeated)
    (universal :
      (package.repeatedMatchedPriorPiecePair survivor repetition).UniversalTargetEquality)
    (proposal :
      (package.repeatedMatchedPriorPiecePair survivor repetition).ProperRepresentativeProposal) :
    package.StageF3 survivor repetition.second :=
  ⟨repetition.first,
    package.repeatedMatchedPriorPiecePair survivor repetition,
    universal, proposal⟩

/-- Construct F5 only after every literal stage is negative for F1--F4.  The
proof uses the actual structural corridor result.  At a repeat, an F2
distinction contradicts the same-stage F2 negative; universal response plus a
proper representative contradicts the same-stage F3 negative. -/
noncomputable def exactF5OfClear (schedule : List package.Stage)
    (scheduleExact : schedule = package.stages.values)
    (clear : ∀ stage, stage ∈ schedule →
      ¬package.F1Stage stage ∧
        ¬package.F2At survivor stage ∧
        ¬package.F3At survivor stage ∧
        ¬package.F4At (ledger := ledger) stage) :
    package.ExactF5 survivor := by
  subst schedule
  have f1Clear : package.F1Clear := fun stage =>
    (clear stage (package.everyStage_mem stage)).1
  cases runExact : package.runColdStructuralCorridor survivor with
  | terminal short =>
      exact .terminal f1Clear short
        (package.terminalF5Support survivor f1Clear short runExact)
  | repeated repetition =>
      let pair := package.repeatedMatchedPriorPiecePair survivor repetition
      cases f2Exact : pair.classifyF2 with
      | distinction distinction =>
          exact False.elim ((clear repetition.second
            (package.everyStage_mem repetition.second)).2.1
              ⟨package.repeatedStageF2 survivor repetition distinction⟩)
      | universal universal =>
          cases f3Exact : pair.classifyF3 universal with
          | compression compression =>
              exact False.elim ((clear repetition.second
                (package.everyStage_mem repetition.second)).2.2.1
                  ⟨package.repeatedStageF3 survivor repetition universal
                    compression.proposal⟩)
          | negative negative =>
              exact .repeated f1Clear repetition universal negative
                (package.repeatedF5Support survivor f1Clear repetition runExact
                  universal negative)

/-- Concrete F2--F5 semantics for the original node-[153] continuation. -/
noncomputable def exactLaterSemantics
    (survivor : package.LocalCorridorSurvivor ledger) :
    package.RequiredF2F5Semantics where
  F2 := package.F2At survivor
  F3 := package.F3At survivor
  F4 := package.F4At (ledger := ledger)
  f2Decidable := package.f2Decidable survivor
  f3Decidable := package.f3Decidable survivor
  f4Decidable := package.f4Decidable (ledger := ledger)
  F2Data := package.F2Data survivor
  F3Data := package.F3Data survivor
  F4Data := package.F4Data (ledger := ledger)
  f2Data := package.f2Data survivor
  f3Data := package.f3Data survivor
  f4Data := package.f4Data (ledger := ledger)
  Germ := package.ScheduledF5 survivor
  germOfClear := fun schedule clear =>
    ⟨schedule, fun scheduleExact =>
      package.exactF5OfClear survivor schedule scheduleExact clear⟩

noncomputable def runExactContinuation
    (survivor : package.LocalCorridorSurvivor ledger) :=
  package.runContinuation (package.exactLaterSemantics survivor)

theorem runExactContinuation_total
    (survivor : package.LocalCorridorSurvivor ledger) :
    (∃ hit data, package.runExactContinuation survivor =
      Core.FiniteFirstFailure.Profile.Result.first hit data) ∨
    (∃ noEvent data, package.runExactContinuation survivor =
      Core.FiniteFirstFailure.Profile.Result.germ noEvent data) :=
  package.runContinuation_total (package.exactLaterSemantics survivor)

theorem exactContinuation_checks
    (survivor : package.LocalCorridorSurvivor ledger) :
    (package.continuationProfile
      (package.exactLaterSemantics survivor)).checks () =
      package.stages.values.length :=
  package.continuation_checks (package.exactLaterSemantics survivor)

end P13WeightedColdRestrictedPrefixPackage

end Erdos64EG.Internal
