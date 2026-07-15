import StructuralExhaustion.CT15.Theorems
import StructuralExhaustion.Core.SmallerObject

namespace StructuralExhaustion.CT15.AdmissibleQuotient

open StructuralExhaustion

universe uAmbient uBranch uCoordinate uBoundary uContext

/-!
# Target rank over audited admissible quotients

This profile separates a raw quotient proposal from admissibility.  A proposal
only assigns quotient codes.  An admissible quotient additionally proves exact
boundary-profile preservation, context-universal target response, and the
manuscript representative clause: if its code is non-injective on the declared
coordinate family, it constructs a genuine certified smaller counterexample.

Consequently a minimal counterexample admits no non-injective admissible
quotient.  CT15 can decide target dependence by a constant negative answer
whose semantic justification is this generic minimality theorem; it never
enumerates quotient proposals or outside contexts.
-/

/-- Exact finite response semantics carried by one declared coordinate
family.  Contexts are mathematical values used only in the universal
admissibility proposition; the CT runner never enumerates them. -/
structure ResponseSystem where
  Coordinate : Type uCoordinate
  BoundaryValue : Type uBoundary
  Context : Type uContext
  boundary : Coordinate → BoundaryValue
  response : Coordinate → Context → Bool

/-- A raw quotient proposal.  It has no preservation or representative
properties until it is audited below. -/
structure Proposal (system : ResponseSystem) where
  code : system.Coordinate → Nat

namespace Proposal

variable {system : ResponseSystem}

/-- Two declared coordinates are identified by the proposed quotient. -/
def Identifies (proposal : Proposal system)
    (left right : system.Coordinate) : Prop :=
  proposal.code left = proposal.code right

end Proposal

/-- The audited quotient contract from the manuscript.  The representative
field is required only when the proposal actually reduces rank.  Its output is
the tactic-independent certified-reduction kernel already shared by CT2 and
CT3. -/
structure Admissible
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    (ctx : Core.MinimalCounterexampleContext P Target)
    (system : ResponseSystem)
    (proposal : Proposal system) where
  preservesBoundary : ∀ {left right}, proposal.Identifies left right →
    system.boundary left = system.boundary right
  targetComplete : ∀ {left right}, proposal.Identifies left right →
    ∀ context, system.response left context = system.response right context
  representedReduction : ¬Function.Injective proposal.code →
    Core.CertifiedReduction ctx

namespace Admissible

variable {P : Core.Problem.{uAmbient, uBranch}}
variable {Target : P.Ambient → Prop}
variable {ctx : Core.MinimalCounterexampleContext P Target}
variable {system : ResponseSystem}
variable {proposal : Proposal system}

/-- An admissible identification cannot produce a boundary-profile blocker. -/
theorem no_boundary_mismatch (quotient : Admissible ctx system proposal)
    {left right : system.Coordinate}
    (identified : proposal.Identifies left right) :
    ¬system.boundary left ≠ system.boundary right :=
  not_not.mpr (quotient.preservesBoundary identified)

/-- An admissible identification cannot produce a target-response blocker in
any outside context. -/
theorem no_target_mismatch (quotient : Admissible ctx system proposal)
    {left right : system.Coordinate}
    (identified : proposal.Identifies left right) (context : system.Context) :
    ¬system.response left context ≠ system.response right context :=
  not_not.mpr (quotient.targetComplete identified context)

/-- Minimality rules out every non-injective admissible quotient. -/
theorem injective (quotient : Admissible ctx system proposal) :
    Function.Injective proposal.code := by
  by_contra noninjective
  exact (quotient.representedReduction noninjective).witness.contradiction

end Admissible

/-- A coordinate is target-dependent exactly when some audited admissible
quotient identifies it with a distinct declared coordinate. -/
def TargetDependent
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    (ctx : Core.MinimalCounterexampleContext P Target)
    (system : ResponseSystem) (coordinate : system.Coordinate) : Prop :=
  ∃ proposal : Proposal system,
    ∃ _quotient : Admissible ctx system proposal,
      ∃ other, other ≠ coordinate ∧ proposal.Identifies other coordinate

/-- The target-dependence predicate is empty for a genuine minimal
counterexample, by the represented-reduction clause of admissibility. -/
theorem not_targetDependent
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    (ctx : Core.MinimalCounterexampleContext P Target)
    (system : ResponseSystem) (coordinate : system.Coordinate) :
    ¬TargetDependent ctx system coordinate := by
  rintro ⟨proposal, quotient, other, distinct, identified⟩
  exact distinct (quotient.injective identified)

/-- Reusable CT15 profile for one explicit finite coordinate family evaluated
under audited admissible quotients. -/
structure Profile
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    (ctx : Core.MinimalCounterexampleContext P Target) where
  system : ResponseSystem.{uCoordinate, uBoundary, uContext}
  coordinates : FinEnum system.Coordinate

namespace Profile

variable {P : Core.Problem.{uAmbient, uBranch}}
variable {Target : P.Ambient → Prop}
variable {ctx : Core.MinimalCounterexampleContext P Target}
variable (profile : Profile ctx)

def spec : CT15.Spec P where
  Coordinate := profile.system.Coordinate
  TargetDependent := fun _ coordinate ↦
    TargetDependent ctx profile.system coordinate
  charge := fun _ _ ↦ 1
  capacity := fun _ ↦ profile.coordinates.card

def capability : CT15.Capability profile.spec where
  coordinates := profile.coordinates
  targetDependentDecidable := fun _ coordinate ↦
    .isFalse (not_targetDependent ctx profile.system coordinate)

def branchInput (_profile : Profile ctx) : CT15.Input P := ctx.toBranchContext

def run := CT15.run profile.spec profile.capability (branchInput profile)

theorem independent (coordinate : profile.system.Coordinate) :
    ¬profile.spec.TargetDependent (branchInput profile) coordinate :=
  not_targetDependent ctx profile.system coordinate

theorem ledgerTotal :
    CT15.ledgerTotal profile.spec profile.capability (branchInput profile) =
      profile.coordinates.card :=
  CT15.ledgerTotal_eq_card_of_charge_eq_one
    profile.spec profile.capability (branchInput profile) (fun _ ↦ rfl)

theorem terminal : profile.run.terminal = .fullRankLedger := by
  apply CT15.run_terminal_eq_fullRankLedger_of_noDrop_of_total_le_capacity
  · exact profile.independent
  · rw [profile.ledgerTotal]
    exact le_rfl

theorem trace : profile.run.trace =
    [.entry, .rankComputation, .rankSplit, .ledgerComputation,
      .ledgerComparison, .fullRankLedgerTerminal] := by
  apply CT15.run_trace_eq_fullRankLedger_of_noDrop_of_total_le_capacity
  · exact profile.independent
  · rw [profile.ledgerTotal]
    exact le_rfl

theorem verified : profile.run.outcome.Valid :=
  CT15.run_verified profile.spec profile.capability (branchInput profile)

theorem total :
    ∃ result, result = profile.run ∧ result.outcome.Valid ∧
      @CT15.Graph.ValidTrace P profile.spec profile.capability
        (branchInput profile)
        result.trace :=
  ⟨profile.run, rfl, profile.verified,
    CT15.run_trace_valid profile.spec profile.capability (branchInput profile)⟩

def budget : Core.PolynomialCheckBudget Unit :=
  CT15.linearCheckBudget profile.spec profile.capability

theorem linearWork :
    profile.budget.checks () ≤ profile.budget.coefficient *
      (profile.budget.size () + 1) ^ profile.budget.degree :=
  profile.budget.bounded ()

end Profile

/-- Opaque proof-carrying package for an admissible-quotient CT15 execution.
Applications can retain this value without re-normalizing the coordinate
family inside `Outcome.Valid`. -/
structure VerifiedStage
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    (ctx : Core.MinimalCounterexampleContext P Target) where
  profile : Profile.{uAmbient, uBranch, uCoordinate, uBoundary, uContext} ctx
  terminal : profile.run.terminal = .fullRankLedger
  trace : profile.run.trace =
    [.entry, .rankComputation, .rankSplit, .ledgerComputation,
      .ledgerComparison, .fullRankLedgerTerminal]
  verified : profile.run.outcome.Valid
  total : ∃ result, result = profile.run ∧ result.outcome.Valid ∧
    @CT15.Graph.ValidTrace P profile.spec profile.capability
      profile.branchInput result.trace
  polynomial : profile.budget.checks () ≤ profile.budget.coefficient *
    (profile.budget.size () + 1) ^ profile.budget.degree

noncomputable def Profile.verifiedStage
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    {ctx : Core.MinimalCounterexampleContext P Target}
    (profile : Profile.{uAmbient, uBranch, uCoordinate, uBoundary, uContext} ctx) :
    VerifiedStage.{uAmbient, uBranch, uCoordinate, uBoundary, uContext} ctx where
  profile := profile
  terminal := profile.terminal
  trace := profile.trace
  verified := profile.verified
  total := profile.total
  polynomial := profile.linearWork

/-- Proposition-valued view of a fixed CT15 profile.  This form is convenient
inside larger verified-prefix propositions because every field is proof data
and the concrete profile remains an explicit parameter. -/
structure VerifiedFor
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    {ctx : Core.MinimalCounterexampleContext P Target}
    (profile : Profile.{uAmbient, uBranch, uCoordinate, uBoundary, uContext} ctx) :
    Prop where
  terminal : profile.run.terminal = .fullRankLedger
  trace : profile.run.trace =
    [.entry, .rankComputation, .rankSplit, .ledgerComputation,
      .ledgerComparison, .fullRankLedgerTerminal]
  verified : profile.run.outcome.Valid
  total : ∃ result, result = profile.run ∧ result.outcome.Valid ∧
    @CT15.Graph.ValidTrace P profile.spec profile.capability
      profile.branchInput result.trace
  polynomial : profile.budget.checks () ≤ profile.budget.coefficient *
    (profile.budget.size () + 1) ^ profile.budget.degree

theorem Profile.verifiedFor
    {P : Core.Problem.{uAmbient, uBranch}}
    {Target : P.Ambient → Prop}
    {ctx : Core.MinimalCounterexampleContext P Target}
    (profile : Profile.{uAmbient, uBranch, uCoordinate, uBoundary, uContext} ctx) :
    VerifiedFor profile where
  terminal := profile.terminal
  trace := profile.trace
  verified := profile.verified
  total := profile.total
  polynomial := profile.linearWork

end StructuralExhaustion.CT15.AdmissibleQuotient
