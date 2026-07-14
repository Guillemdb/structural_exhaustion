import StructuralExhaustion.CT15.Theorems

namespace StructuralExhaustion.CT15.BaselineDemand

open StructuralExhaustion

universe uAmbient uBranch uCoordinate

/-!
# Certified finite baseline demands

A baseline demand is an explicit finite family of target coordinates already
proved independent by the mathematical application, together with the exact
baseline budget and its deficit.  This profile turns that author data into the
canonical CT15 full-rank ledger.  The machine scans only the declared
coordinate list; it never constructs subsets, target states, or graphs.
-/

structure Profile (P : Core.Problem.{uAmbient, uBranch}) where
  Coordinate : Type uCoordinate
  coordinates : FinEnum Coordinate
  TargetDependent : Core.BranchContext P → Coordinate → Prop
  independent : ∀ input coordinate, ¬ TargetDependent input coordinate
  baseline : Core.BranchContext P → Nat
  deficit : Core.BranchContext P → Nat
  deficit_le_baseline : ∀ input, deficit input ≤ baseline input
  lowerBound : ∀ input,
    baseline input - deficit input ≤ coordinates.card

namespace Profile

variable {P : Core.Problem.{uAmbient, uBranch}}
variable (profile : Profile.{uAmbient, uBranch, uCoordinate} P)

def spec : CT15.Spec P where
  Coordinate := profile.Coordinate
  TargetDependent := profile.TargetDependent
  charge := fun _ _ => 1
  capacity := fun _ => profile.coordinates.card

def capability : CT15.Capability profile.spec where
  coordinates := profile.coordinates
  targetDependentDecidable := fun input coordinate =>
    .isFalse (profile.independent input coordinate)

def run (input : Core.BranchContext P) :=
  CT15.run profile.spec profile.capability input

theorem ledgerTotal (input : Core.BranchContext P) :
    CT15.ledgerTotal profile.spec profile.capability input =
      profile.coordinates.card :=
  CT15.ledgerTotal_eq_card_of_charge_eq_one
    profile.spec profile.capability input (fun _ => rfl)

theorem terminal (input : Core.BranchContext P) :
    (profile.run input).terminal = .fullRankLedger := by
  apply CT15.run_terminal_eq_fullRankLedger_of_noDrop_of_total_le_capacity
  · exact profile.independent input
  · rw [profile.ledgerTotal input]
    change profile.coordinates.card ≤ profile.coordinates.card
    exact le_rfl

theorem trace (input : Core.BranchContext P) :
    (profile.run input).trace =
      [.entry, .rankComputation, .rankSplit, .ledgerComputation,
        .ledgerComparison, .fullRankLedgerTerminal] := by
  apply CT15.run_trace_eq_fullRankLedger_of_noDrop_of_total_le_capacity
  · exact profile.independent input
  · rw [profile.ledgerTotal input]
    change profile.coordinates.card ≤ profile.coordinates.card
    exact le_rfl

theorem verified (input : Core.BranchContext P) :
    (profile.run input).outcome.Valid :=
  CT15.run_verified profile.spec profile.capability input

theorem traceValid (input : Core.BranchContext P) :
    @CT15.Graph.ValidTrace P profile.spec profile.capability input
      (profile.run input).trace :=
  CT15.run_trace_valid profile.spec profile.capability input

theorem total (input : Core.BranchContext P) :
    ∃ result, result = profile.run input ∧
      result.outcome.Valid ∧
      @CT15.Graph.ValidTrace P profile.spec profile.capability input
        result.trace :=
  ⟨profile.run input, rfl, profile.verified input, profile.traceValid input⟩

def budget (_input : Core.BranchContext P) :
    Core.PolynomialCheckBudget Unit :=
  CT15.linearCheckBudget profile.spec profile.capability

theorem linearWork (input : Core.BranchContext P) :
    (profile.budget input).checks () ≤
      (profile.budget input).coefficient *
        ((profile.budget input).size () + 1) ^
          (profile.budget input).degree :=
  (profile.budget input).bounded ()

/-- All semantic and execution clauses retained by a verified baseline-demand
stage. -/
structure VerifiedStage (input : Core.BranchContext P) : Prop where
  independent : ∀ coordinate,
    ¬ profile.TargetDependent input coordinate
  lowerBound : profile.baseline input - profile.deficit input ≤
    profile.coordinates.card
  deficitLeBaseline : profile.deficit input ≤ profile.baseline input
  terminal : (profile.run input).terminal = .fullRankLedger
  trace : (profile.run input).trace =
    [.entry, .rankComputation, .rankSplit, .ledgerComputation,
      .ledgerComparison, .fullRankLedgerTerminal]
  verified : (profile.run input).outcome.Valid
  ledgerTotal : CT15.ledgerTotal profile.spec profile.capability input =
    profile.coordinates.card
  total : ∃ result, result = profile.run input ∧
    result.outcome.Valid ∧
    @CT15.Graph.ValidTrace P profile.spec profile.capability input result.trace
  linearWork : (profile.budget input).checks () ≤
    (profile.budget input).coefficient *
      ((profile.budget input).size () + 1) ^
        (profile.budget input).degree

def verifiedStage (input : Core.BranchContext P) :
    profile.VerifiedStage input where
  independent := profile.independent input
  lowerBound := profile.lowerBound input
  deficitLeBaseline := profile.deficit_le_baseline input
  terminal := profile.terminal input
  trace := profile.trace input
  verified := profile.verified input
  ledgerTotal := profile.ledgerTotal input
  total := profile.total input
  linearWork := profile.linearWork input

end Profile

end StructuralExhaustion.CT15.BaselineDemand
