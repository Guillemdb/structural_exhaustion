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

/-- Execute the public CT14 runner on one literal site. -/
def run {P : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext P) (site : Site) :
    CT14.ExecutionResult (profile.capability P site) context :=
  CT14.run (profile.capability P site) context (profile.input context site)

/-- Positive branch: the assigned certificate is retained together with the
complete singleton CT14 audit. -/
structure Marked {P : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext P) (site : Site) : Type uCertificate where
  certificate : profile.Certificate site
  present : profile.assigned site = some certificate
  terminal : (profile.run context site).terminal = .capacity
  trace : (profile.run context site).trace =
    [.entry, .lowerMass, .memberScan, .upperCapacity, .comparison,
      .capacityTerminal]
  verified : (profile.run context site).outcome.Valid
  traceValid : @CT14.Graph.ValidTrace P (profile.capability P site) context
    (profile.run context site).trace
  total : ∃ result : CT14.ExecutionResult (profile.capability P site) context,
    result.outcome.Valid ∧
      @CT14.Graph.ValidTrace P (profile.capability P site) context result.trace

/-- Negative branch: the exact same site is retained with proof that its
assigned-certificate slot is empty. -/
structure Residual {P : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext P) (site : Site) : Prop where
  missing : profile.assigned site = none
  terminal : (profile.run context site).terminal = .missingLabel
  trace : (profile.run context site).trace =
    [.entry, .lowerMass, .memberScan, .missingLabelTerminal]
  verified : (profile.run context site).outcome.Valid
  traceValid : @CT14.Graph.ValidTrace P (profile.capability P site) context
    (profile.run context site).trace
  total : ∃ result : CT14.ExecutionResult (profile.capability P site) context,
    result.outcome.Valid ∧
      @CT14.Graph.ValidTrace P (profile.capability P site) context result.trace

/-- Exact per-site outcome.  It is a decision about supplied local data, not
about whether some certificate could exist elsewhere. -/
inductive Decision (profile : Profile.{uSite, uCertificate} Site)
    {P : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext P) (site : Site) : Type uCertificate where
  | marked (result : profile.Marked context site) :
      Decision profile context site
  | residual (result : profile.Residual context site) :
      Decision profile context site

/-- Compute and audit the assigned-certificate branch at one site. -/
def decide {P : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext P) (site : Site) :
    profile.Decision context site := by
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
          (profile.input context site)
        total := CT14.run_total (profile.capability P site) context
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
          (profile.input context site)
        total := CT14.run_total (profile.capability P site) context
          (profile.input context site) }

/-- Every actual site takes exactly one of the two assigned-data branches. -/
theorem marked_or_residual {P : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext P) (site : Site) :
    Nonempty (profile.Marked context site) ∨ profile.Residual context site := by
  cases profile.decide context site with
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

/-- The complete reusable stage retains the independently audited decision
at every site and a linear work bound in the supplied site count. -/
structure VerifiedStage {P : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext P) : Prop where
  exhaustive : ∀ site : Site,
    Nonempty (profile.Marked context site) ∨ profile.Residual context site
  polynomial : profile.checks ≤
    profile.budget.coefficient *
      (profile.budget.size () + 1) ^ profile.budget.degree

def verifiedStage {P : Core.Problem.{uAmbient, uBranch}}
    (context : Core.BranchContext P) : profile.VerifiedStage context where
  exhaustive := profile.marked_or_residual context
  polynomial := profile.budget.bounded ()

end Profile

end StructuralExhaustion.Graph.FiniteCertificateMarking
