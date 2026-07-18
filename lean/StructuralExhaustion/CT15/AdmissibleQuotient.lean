import StructuralExhaustion.CT15.Theorems
import StructuralExhaustion.Core.SmallerObject
import StructuralExhaustion.Core.ZeroWorkBudget

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

/-- A declared subfamily survives the complete admissible quotient system
exactly when every admissible quotient is label-injective on that subfamily.
This is the manuscript notion of rank independence; it quantifies over
quotients propositionally and never enumerates them. -/
def declaredCoordinates : Finset profile.system.Coordinate :=
  @List.toFinset profile.system.Coordinate profile.coordinates.decEq
    profile.coordinates.orderedValues

def Survives (family : Finset profile.system.Coordinate) : Prop :=
  family ⊆ profile.declaredCoordinates ∧
    ∀ (proposal : Proposal profile.system),
      Admissible ctx profile.system proposal →
        Set.InjOn proposal.code (family : Set profile.system.Coordinate)

theorem declaredCoordinates_card :
    profile.declaredCoordinates.card = profile.coordinates.card := by
  unfold declaredCoordinates
  rw [@List.toFinset_card_of_nodup _ profile.coordinates.decEq _
    profile.coordinates.nodup_orderedValues]
  exact profile.coordinates.orderedValues_length

/-- Exact functional-quotient target rank. `findGreatest` ranges only over
the possible cardinalities `0,...,|coordinates|`; its predicate is
proof-level existence of a surviving family, so neither subfamilies nor
quotients are evaluated. -/
noncomputable def targetRank : Nat := by
  classical
  exact Nat.findGreatest
    (fun size => ∃ family : Finset profile.system.Coordinate,
      profile.Survives family ∧ family.card = size)
    profile.coordinates.card

theorem surviving_card_le_coordinates
    {family : Finset profile.system.Coordinate}
    (survives : profile.Survives family) :
    family.card ≤ profile.coordinates.card := by
  calc
    family.card ≤ profile.declaredCoordinates.card :=
      Finset.card_le_card survives.1
    _ = profile.coordinates.card := profile.declaredCoordinates_card

theorem targetRank_le_coordinates :
    profile.targetRank ≤ profile.coordinates.card := by
  unfold targetRank
  classical
  exact Nat.findGreatest_le _

theorem surviving_card_le_targetRank
    {family : Finset profile.system.Coordinate}
    (survives : profile.Survives family) :
    family.card ≤ profile.targetRank := by
  unfold targetRank
  classical
  apply Nat.le_findGreatest (profile.surviving_card_le_coordinates survives)
  exact ⟨family, survives, rfl⟩

/-- The bounded maximum is attained by an actual surviving declared subfamily, so
`targetRank` is literally the maximum in the manuscript definition. -/
theorem exists_surviving_card_eq_targetRank :
    ∃ family : Finset profile.system.Coordinate,
      profile.Survives family ∧ family.card = profile.targetRank := by
  unfold targetRank
  classical
  apply Nat.findGreatest_spec
    (P := fun size => ∃ family : Finset profile.system.Coordinate,
      profile.Survives family ∧ family.card = size)
    (m := 0) (n := profile.coordinates.card)
  · omega
  · refine ⟨∅, ?_, rfl⟩
    refine ⟨Finset.empty_subset _, ?_⟩
    intro proposal quotient
    simpa using Set.injOn_empty proposal.code

/-- Exact exhaustive target-rank split on the declared coordinate family.
The dropped constructor is the manuscript's rank-loss edge; the full
constructor is equality with the complete raw schedule. -/
inductive RankDecision where
  | dropped (rank_lt : profile.targetRank < profile.coordinates.card)
  | full (rank_eq : profile.targetRank = profile.coordinates.card)

/-- Decide only the two existing rank-test edges.  The comparison is
proof-level because `targetRank` is noncomputable; no surviving family or
quotient system is evaluated. -/
noncomputable def rankDecision : profile.RankDecision := by
  classical
  by_cases dropped : profile.targetRank < profile.coordinates.card
  · exact .dropped dropped
  · exact .full (Nat.le_antisymm profile.targetRank_le_coordinates
      (Nat.le_of_not_gt dropped))

theorem rankDecision_exhaustive :
    profile.targetRank < profile.coordinates.card ∨
      profile.targetRank = profile.coordinates.card := by
  cases profile.rankDecision with
  | dropped rank_lt => exact Or.inl rank_lt
  | full rank_eq => exact Or.inr rank_eq

/-- The rank split performs no executable search: it compares a proof-level
maximum already supplied by the preceding rank-definition node. -/
def rankDecisionBudget : Core.PolynomialCheckBudget Unit :=
  Core.PolynomialCheckBudget.zero (fun _ => profile.coordinates.card)

/-- A finite functional circuit witnessing one rank-reducing identification.
The singleton basis is the elementary functional dependence extracted from a
non-injective quotient: the determined coordinate has the same quotient value
as one distinct earlier coordinate. -/
structure PairCircuit where
  proposal : Proposal profile.system
  quotient : Admissible ctx profile.system proposal
  determined : profile.system.Coordinate
  basisCoordinate : profile.system.Coordinate
  determined_mem : determined ∈ profile.declaredCoordinates
  basis_mem : basisCoordinate ∈ profile.declaredCoordinates
  distinct : basisCoordinate ≠ determined
  determines : proposal.code basisCoordinate = proposal.code determined

namespace PairCircuit

variable {profile : Profile ctx}

def basis (circuit : profile.PairCircuit) : Finset profile.system.Coordinate :=
  @List.toFinset profile.system.Coordinate profile.coordinates.decEq
    [circuit.basisCoordinate]

theorem basis_subset_declared (circuit : profile.PairCircuit) :
    circuit.basis ⊆ profile.declaredCoordinates := by
  intro coordinate member
  have equal : coordinate = circuit.basisCoordinate := by
    simpa [basis] using member
  simpa [equal] using circuit.basis_mem

theorem determined_not_mem_basis (circuit : profile.PairCircuit) :
    circuit.determined ∉ circuit.basis := by
  simpa [basis, ne_comm] using circuit.distinct

/-- The two coordinates identified by an admitted pair circuit have identical
target response in every declared outside context.  This is a projection of
the quotient's audited target-completeness field; no context collection is
constructed or scanned. -/
theorem contextUniversal (circuit : profile.PairCircuit) :
    ∀ context : profile.system.Context,
      profile.system.response circuit.basisCoordinate context =
        profile.system.response circuit.determined context :=
  circuit.quotient.targetComplete circuit.determines

/-- The exact two edges of a manuscript context-validity test.  A defect
retains one concrete distinguishing context; the other edge retains the
universal response theorem. -/
inductive ContextDecision (circuit : profile.PairCircuit) where
  | defective (context : profile.system.Context)
      (mismatch : profile.system.response circuit.basisCoordinate context ≠
        profile.system.response circuit.determined context)
  | universal (allContexts : ∀ context : profile.system.Context,
      profile.system.response circuit.basisCoordinate context =
        profile.system.response circuit.determined context)

/-- Proof-carrying payload of the target-defect edge.  It retains exactly one
declared outside context and the response mismatch found there. -/
structure ContextDefect (circuit : profile.PairCircuit) where
  context : profile.system.Context
  mismatch : profile.system.response circuit.basisCoordinate context ≠
    profile.system.response circuit.determined context

namespace ContextDefect

theorem toExists {circuit : profile.PairCircuit}
    (defect : circuit.ContextDefect) :
    ∃ context : profile.system.Context,
      profile.system.response circuit.basisCoordinate context ≠
        profile.system.response circuit.determined context :=
  ⟨defect.context, defect.mismatch⟩

/-- A concrete defect cannot occur after the quotient has already passed the
admissibility audit. -/
theorem impossible {circuit : profile.PairCircuit}
    (defect : circuit.ContextDefect) : False :=
  defect.mismatch (circuit.contextUniversal defect.context)

end ContextDefect

/-- An admitted pair circuit necessarily takes the universal edge.  This is
still represented by the exact two-constructor decision type so downstream
diagram routing cannot invent a third case. -/
def contextDecision (circuit : profile.PairCircuit) : circuit.ContextDecision :=
  .universal circuit.contextUniversal

theorem contextDecision_isUniversal (circuit : profile.PairCircuit) :
    circuit.contextDecision = .universal circuit.contextUniversal := rfl

theorem noContextDefect (circuit : profile.PairCircuit) :
    ¬∃ context : profile.system.Context,
      profile.system.response circuit.basisCoordinate context ≠
        profile.system.response circuit.determined context := by
  rintro ⟨context, mismatch⟩
  exact mismatch (circuit.contextUniversal context)

/-- The pair identification is genuinely rank reducing. -/
theorem proposal_not_injective (circuit : profile.PairCircuit) :
    ¬Function.Injective circuit.proposal.code := by
  intro injective
  exact circuit.distinct (injective circuit.determines)

/-- The representative clause of quotient admissibility supplies the strictly
smaller baseline object and target transport required by the compression
branch. -/
def smallerRepresentative (circuit : profile.PairCircuit) :
    Core.CertifiedReduction ctx :=
  circuit.quotient.representedReduction circuit.proposal_not_injective

/-- The proper-compression edge carried by an admitted non-injective circuit
closes immediately by the generic certified-reduction minimality kernel.  The
representative is already part of quotient admission; this theorem performs
no search or finite scan. -/
theorem properCompression_impossible (circuit : profile.PairCircuit) : False :=
  circuit.smallerRepresentative.impossible

/-- Exact two-edge representation of the smaller-representative test.  The
negative constructor retains the proposition that no certified representative
exists; an already admitted non-injective circuit necessarily takes the
positive constructor. -/
inductive RepresentativeDecision (circuit : profile.PairCircuit) where
  | available (representative : Core.CertifiedReduction ctx)
  | unavailable (missing : ¬Nonempty (Core.CertifiedReduction ctx))

def representativeDecision (circuit : profile.PairCircuit) :
    circuit.RepresentativeDecision :=
  .available circuit.smallerRepresentative

theorem representativeDecision_isAvailable (circuit : profile.PairCircuit) :
    circuit.representativeDecision =
      .available circuit.smallerRepresentative := rfl

/-- Projecting the representative already certified by quotient admission has
zero executable cost. -/
def representativeDecisionBudget (_circuit : profile.PairCircuit) :
    Core.PolynomialCheckBudget Unit :=
  Core.PolynomialCheckBudget.zero (fun _ => profile.coordinates.card)

/-- Projecting context universality from an already admitted quotient performs
no executable work. -/
def contextDecisionBudget (_circuit : profile.PairCircuit) :
    Core.PolynomialCheckBudget Unit :=
  Core.PolynomialCheckBudget.zero (fun _ => profile.coordinates.card)

end PairCircuit

/-- A strict loss of the exact maximum produces a concrete finite functional
dependence circuit.  The proof is classical but does not execute a powerset or
quotient search: it eliminates the negation of universal survival. -/
theorem pairCircuit_nonempty_of_rankDrop
    (rankDrop : profile.targetRank < profile.coordinates.card) :
    Nonempty profile.PairCircuit := by
  classical
  have notSurvives : ¬profile.Survives profile.declaredCoordinates := by
    intro survives
    have lower := profile.surviving_card_le_targetRank survives
    rw [profile.declaredCoordinates_card] at lower
    exact (Nat.not_lt_of_ge lower) rankDrop
  have noninjective : ∃ (proposal : Proposal profile.system),
      ∃ quotient : Admissible ctx profile.system proposal,
        ¬Set.InjOn proposal.code
          (profile.declaredCoordinates : Set profile.system.Coordinate) := by
    by_contra absent
    apply notSurvives
    refine ⟨Finset.Subset.rfl, ?_⟩
    intro proposal quotient
    by_contra notInjOn
    exact absent ⟨proposal, quotient, notInjOn⟩
  obtain ⟨proposal, quotient, notInjOn⟩ := noninjective
  simp only [Set.InjOn] at notInjOn
  push Not at notInjOn
  obtain ⟨left, leftMem, right, rightMem, identified, distinct⟩ := notInjOn
  exact ⟨{
    proposal := proposal
    quotient := quotient
    determined := right
    basisCoordinate := left
    determined_mem := rightMem
    basis_mem := leftMem
    distinct := distinct
    determines := identified
  }⟩

noncomputable def pairCircuitOfRankDrop
    (rankDrop : profile.targetRank < profile.coordinates.card) :
    profile.PairCircuit :=
  Classical.choice (profile.pairCircuit_nonempty_of_rankDrop rankDrop)

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
