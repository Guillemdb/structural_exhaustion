import Mathlib.Tactic
import StructuralExhaustion.CT14.Automation
import StructuralExhaustion.Core.WorkBudget

namespace StructuralExhaustion.Graph.FiniteCertificateMarking

open StructuralExhaustion

universe uSite uCertificate uAmbient uBranch

/-!
# Finite assigned-certificate marking

This profile decides whether a certificate is present in already supplied
local data.  It does not search a certificate space.  For every site the
framework executes CT14 on a singleton member schedule whose optional label
is present exactly when the supplied certificate is present.  The two
possible outputs retain either the certificate itself or the literal
`Option.none` equation for the same site.

The complete family is processed site by site.  Hence both marked and
unmarked sites are retained; a first missing certificate never suppresses
the marked decisions at later sites.
-/

/-- Static local data: an explicit finite site schedule and, at each site,
the certificate already assigned by the predecessor residual. -/
structure Profile (Site : Type uSite) where
  sites : FinEnum Site
  Certificate : Site → Type uCertificate
  assigned : (site : Site) → Option (Certificate site)

namespace Profile

variable {Site : Type uSite} (profile : Profile.{uSite, uCertificate} Site)

/-- The singleton CT14 capability that observes assigned-certificate
presence at one fixed site. -/
def capability (P : Core.Problem.{uAmbient, uBranch}) (site : Site) :
    CT14.Capability P where
  Member := Unit
  members := Core.Enumeration.unit
  Label := Unit
  labelDecidableEq := inferInstance
  memberLowerMass := fun _context _member => 0
  memberCapacity := fun _context _member => some 0
  memberLabel := fun _context _member => (profile.assigned site).map fun _ => ()

def input {P : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext P) (site : Site) :
    CT14.Input (profile.capability P site) context := ⟨⟩

/-- Positive branch indexed by the literal CT14 result retained by the
accumulated transition ledger. -/
structure Marked {P : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext P) (site : Site)
    (execution : CT14.ExecutionResult (profile.capability P site) context) :
    Type uCertificate where
  certificate : profile.Certificate site
  present : profile.assigned site = some certificate
  terminal : execution.terminal = .capacity
  trace : execution.trace =
    [.entry, .lowerMass, .memberScan, .upperCapacity, .comparison,
      .capacityTerminal]
  verified : execution.outcome.Valid
  traceValid : @CT14.Graph.ValidTrace P (profile.capability P site) context
    execution.trace

/-- Negative branch indexed by the same literal target result. -/
structure Residual {P : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext P) (site : Site)
    (execution : CT14.ExecutionResult (profile.capability P site) context) :
    Prop where
  missing : profile.assigned site = none
  terminal : execution.terminal = .missingLabel
  trace : execution.trace =
    [.entry, .lowerMass, .memberScan, .missingLabelTerminal]
  verified : execution.outcome.Valid
  traceValid : @CT14.Graph.ValidTrace P (profile.capability P site) context
    execution.trace

/-- Exact per-site outcome.  It is a decision about supplied local data, not
about whether some certificate could exist elsewhere. -/
inductive Decision (profile : Profile.{uSite, uCertificate} Site)
    {P : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext P) (site : Site)
    (execution : CT14.ExecutionResult (profile.capability P site) context) :
    Type uCertificate where
  | marked (result : profile.Marked context site execution) :
      Decision profile context site execution
  | residual (result : profile.Residual context site execution) :
      Decision profile context site execution

/-- Classify one already executed singleton CT14 result.  `exactRun` is the
bridge from the accumulated transition target; the graph layer never launches
a second runner. -/
def decideExecution {P : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext P) (site : Site)
    (execution : CT14.ExecutionResult (profile.capability P site) context)
    (exactRun : execution = CT14.run (profile.capability P site) context
      (profile.input context site)) :
    profile.Decision context site execution := by
  subst execution
  cases equation : profile.assigned site with
  | none =>
      exact .residual {
        missing := equation
        terminal := by
          apply CT14.run_terminal_missingLabel_of_bounded_of_missing
          · intro member
            exact ⟨0, rfl⟩
          · exact ⟨(), by simp [capability, equation]⟩
        trace := by
          apply CT14.run_trace_missingLabel_of_bounded_of_missing
          · intro member
            exact ⟨0, rfl⟩
          · exact ⟨(), by simp [capability, equation]⟩
        verified := CT14.run_verified (profile.capability P site) context
          (profile.input context site)
        traceValid := CT14.run_trace_valid (profile.capability P site) context
          (profile.input context site) }
  | some certificate =>
      exact .marked {
        certificate := certificate
        present := equation
        terminal := by
          apply CT14.run_terminal_capacity_of_complete
          · intro member
            exact ⟨0, rfl⟩
          · intro member
            exact ⟨(), by simp [capability, equation]⟩
          · simp [CT14.lowerMass, CT14.upperCapacity, capability]
        trace := by
          apply CT14.run_trace_capacity_of_complete
          · intro member
            exact ⟨0, rfl⟩
          · intro member
            exact ⟨(), by simp [capability, equation]⟩
          · simp [CT14.lowerMass, CT14.upperCapacity, capability]
        verified := CT14.run_verified (profile.capability P site) context
          (profile.input context site)
        traceValid := CT14.run_trace_valid (profile.capability P site) context
          (profile.input context site) }

/-- Every literal transitioned site takes exactly one assigned-data branch. -/
theorem marked_or_residual_of_execution
    {P : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext P) (site : Site)
    (execution : CT14.ExecutionResult (profile.capability P site) context)
    (exactRun : execution = CT14.run (profile.capability P site) context
      (profile.input context site)) :
    Nonempty (profile.Marked context site execution) ∨
      profile.Residual context site execution := by
  cases profile.decideExecution context site execution exactRun with
  | marked result => exact Or.inl ⟨result⟩
  | residual result => exact Or.inr result

/-- Six primitive operations per site: schedule the singleton, compute lower
mass, inspect capacity, inspect certificate presence, compute upper capacity,
and compare. -/
def checks : Nat := 6 * profile.sites.card

def budget : Core.PolynomialCheckBudget Unit where
  size := fun _ => profile.sites.card
  checks := fun _ => profile.checks
  coefficient := 6
  degree := 1
  bounded := by
    intro _unit
    simp [checks]

/-- The complete reusable stage is indexed by the pointwise CT14 results
retained in an accumulated transition ledger. -/
structure VerifiedExecutionStage {P : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext P)
    (execution : (site : Site) →
      CT14.ExecutionResult (profile.capability P site) context) : Prop where
  exactRun : ∀ site, execution site =
    CT14.run (profile.capability P site) context (profile.input context site)
  exhaustive : ∀ site : Site,
    Nonempty (profile.Marked context site (execution site)) ∨
      profile.Residual context site (execution site)
  polynomial : profile.checks ≤
    profile.budget.coefficient *
      (profile.budget.size () + 1) ^ profile.budget.degree

def verifiedExecutionStage {P : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext P)
    (execution : (site : Site) →
      CT14.ExecutionResult (profile.capability P site) context)
    (exactRun : ∀ site, execution site =
      CT14.run (profile.capability P site) context
        (profile.input context site)) :
    profile.VerifiedExecutionStage context execution where
  exactRun := exactRun
  exhaustive := fun site => profile.marked_or_residual_of_execution
    context site (execution site) (exactRun site)
  polynomial := profile.budget.bounded ()

end Profile

end StructuralExhaustion.Graph.FiniteCertificateMarking
