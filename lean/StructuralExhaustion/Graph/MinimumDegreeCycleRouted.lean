import StructuralExhaustion.Core.MinimalSelection
import StructuralExhaustion.Graph.EdgeRootedReturn
import StructuralExhaustion.Graph.MinimumDegreeCycle
import StructuralExhaustion.Routes.CT1ToCT2

namespace StructuralExhaustion.Graph.MinimumDegreeCycle.StaticInput

open StructuralExhaustion

universe uVertex uBranch uCode

variable {V : Type uVertex}
variable {BranchState : FiniteObject V → Type uBranch}

/-!
# Routed minimum-degree cycle profiles

This module owns the reusable proof-carrying edge-rooted CT1 target and the
certificate-CT1-to-local-deletion-CT2 composition for every
`MinimumDegreeCycle.StaticInput`.  Applications select a cycle-length
predicate and retain only theorem-specific arithmetic and statement bridges.
-/

/-! ## Edge-rooted cycle target -/

/-- The local return-length predicate induced by a cycle-length target. -/
def ReturnLengthOK (input : StaticInput V BranchState) (length : Nat) : Prop :=
  input.LengthOK (length + 1)

/-- A proof-carrying return certificate for the profile's cycle target. -/
abbrev RootedReturn (input : StaticInput V BranchState)
    (object : FiniteObject V) :=
  EdgeRootedReturn object.graph input.ReturnLengthOK

/-- Existence of one accepted edge-rooted return. -/
abbrev HasRootedReturn (input : StaticInput V BranchState)
    (object : FiniteObject V) :=
  HasEdgeRootedReturn object.graph input.ReturnLengthOK

/-- The profile's cycle target is exactly its edge-rooted return target. -/
theorem target_iff_hasRootedReturn (input : StaticInput V BranchState)
    (object : FiniteObject V) :
    input.Target object ↔ input.HasRootedReturn object :=
  hasCycleWithLength_iff_hasEdgeRootedReturn object.graph input.LengthOK

/-- Exact avoiding form of the profile target over every oriented root edge. -/
theorem not_target_iff_returnSets_disjoint
    (input : StaticInput V BranchState) (object : FiniteObject V) :
    ¬ input.Target object ↔
      ∀ dart : object.graph.Dart,
        Disjoint (edgeReturnSet object.graph dart)
          {length | input.ReturnLengthOK length} := by
  simpa [Target, ReturnLengthOK] using
    (noCycleWithLength_iff_returnSets_disjoint object.graph input.LengthOK)

/-- Certificate-driven CT1 encoding whose code is one accepted rooted return. -/
def edgeRootedEncoding (input : StaticInput V BranchState) :
    CT1.TargetCertificateEncoding (P := input.problem) input.Target where
  Code := fun object => input.RootedReturn object
  Accepts := fun _object _return => True
  encode := by
    intro object target
    obtain ⟨certificate⟩ := (input.target_iff_hasRootedReturn object).mp target
    exact ⟨certificate, trivial⟩
  decode := by
    intro object certificate _accepted
    exact (input.target_iff_hasRootedReturn object).mpr ⟨certificate⟩

abbrev edgeRootedSpec (input : StaticInput V BranchState) :=
  input.edgeRootedEncoding.spec

abbrev edgeRootedBridge (input : StaticInput V BranchState) :=
  input.edgeRootedEncoding.bridge

/-- CT1 input retaining an application-supplied branch state. -/
def edgeRootedInput (input : StaticInput V BranchState)
    (object : FiniteObject V) (baseline : input.problem.Baseline object)
    (state : BranchState object) : CT1.Input input.problem where
  context := ⟨object, baseline, state⟩

/-- Exact C1 execution from one edge-rooted return certificate. -/
def runRootedReturnCT1 (input : StaticInput V BranchState)
    (object : FiniteObject V) (baseline : input.problem.Baseline object)
    (state : BranchState object) (certificate : input.RootedReturn object) :
    CT1.CertifiedC1Run input.edgeRootedSpec
      (input.edgeRootedInput object baseline state) :=
  input.edgeRootedEncoding.run
    (input.edgeRootedInput object baseline state) certificate trivial

/-- Delete the first edge of a supplied target cycle and validate the resulting
rooted return through the same CT1 encoding. -/
def runCycleAsRootedReturnCT1 (input : StaticInput V BranchState)
    (object : FiniteObject V) (baseline : input.problem.Baseline object)
    (state : BranchState object)
    (cycle : CycleWithLength object.graph input.LengthOK) :
    CT1.CertifiedC1Run input.edgeRootedSpec
      (input.edgeRootedInput object baseline state) :=
  input.runRootedReturnCT1 object baseline state
    (EdgeRootedReturn.ofCycle cycle)

/-- Exact proof-carrying CT1 avoiding execution; no return universe is
materialized. -/
def runAvoidingRootedReturnCT1 (input : StaticInput V BranchState)
    (object : FiniteObject V) (baseline : input.problem.Baseline object)
    (state : BranchState object) (avoids : ¬ input.Target object) :
    CT1.CertifiedAvoidingRun input.edgeRootedSpec
      (input.edgeRootedInput object baseline state) :=
  input.edgeRootedEncoding.runAvoiding
    (input.edgeRootedInput object baseline state) avoids

/-- The avoiding CT1 outcome yields exact disjointness of every local return
set from the induced predecessor-length target. -/
theorem runAvoidingRootedReturnCT1_returnSets_disjoint
    (input : StaticInput V BranchState)
    (object : FiniteObject V) (baseline : input.problem.Baseline object)
    (state : BranchState object) (avoids : ¬ input.Target object) :
    ∀ dart : object.graph.Dart,
      Disjoint (edgeReturnSet object.graph dart)
        {length | input.ReturnLengthOK length} :=
  (input.not_target_iff_returnSets_disjoint object).mp
    (input.edgeRootedEncoding.not_publicTarget_of_runAvoiding
      (input.edgeRootedInput object baseline state) avoids)

/-! ## Reusable CT1-to-local-CT2 composition -/

/-- Combine any proof-carrying encoding of this cycle target with the graph
profile's local dart-deletion capability. -/
def certificateDeletionProfile (input : StaticInput V BranchState)
    (encoding : CT1.TargetCertificateEncoding (P := input.problem)
      input.Target) :
    Routes.CT1ToCT2.LocalDeletion.CertificateProfile
      (P := input.problem) input.Target where
  encoding := encoding
  capability := input.ct2Capability
  closure := input.ct2DeletionRule

/-- Route profile using the ordinary concrete-cycle certificate. -/
def cycleDeletionProfile (input : StaticInput V BranchState) :=
  input.certificateDeletionProfile input.targetEncoding

/-- Route profile using an edge-rooted return certificate. -/
def edgeRootedDeletionProfile (input : StaticInput V BranchState) :=
  input.certificateDeletionProfile input.edgeRootedEncoding

/-- Routed deletion criticality for any proof-carrying encoding of the same
cycle target. -/
theorem routedDart_has_tight_endpoint
    (input : StaticInput V BranchState)
    (encoding : CT1.TargetCertificateEncoding (P := input.problem)
      input.Target)
    (ctx : Core.MinimalCounterexampleContext input.problem input.Target)
    (dart : ctx.G.graph.Dart) :
    ctx.G.degree dart.fst = input.minimumDegree ∨
      ctx.G.degree dart.snd = input.minimumDegree := by
  let profile := input.certificateDeletionProfile encoding
  have notEligible :=
    Routes.CT1ToCT2.LocalDeletion.disabled_sound profile.capability
      (profile.targetMinimality ctx) profile.routedClosure
      (profile.currentAvoiding ctx) (profile.sourceLedger ctx)
      (profile.transition_not_enabled ctx) dart
  have notSlack : ¬(input.minimumDegree + 1 ≤ ctx.G.degree dart.fst ∧
      input.minimumDegree + 1 ≤ ctx.G.degree dart.snd) := by
    rcases notEligible with notProper | notAdmissible
    · exact notProper
    · exact (notAdmissible trivial).elim
  have fstLower : input.minimumDegree ≤ ctx.G.degree dart.fst :=
    ctx.baseline.trans (ctx.G.minDegree_le_degree dart.fst)
  have sndLower : input.minimumDegree ≤ ctx.G.degree dart.snd :=
    ctx.baseline.trans (ctx.G.minDegree_le_degree dart.snd)
  omega

/-- Vertices with one unit of degree slack form an independent set. -/
theorem routedHighDegree_independent
    (input : StaticInput V BranchState)
    (encoding : CT1.TargetCertificateEncoding (P := input.problem)
      input.Target)
    (ctx : Core.MinimalCounterexampleContext input.problem input.Target)
    {left right : V}
    (leftHigh : input.minimumDegree + 1 ≤ ctx.G.degree left)
    (rightHigh : input.minimumDegree + 1 ≤ ctx.G.degree right) :
    ¬ ctx.G.graph.Adj left right := by
  intro adjacent
  have critical := input.routedDart_has_tight_endpoint encoding ctx
    ⟨(left, right), adjacent⟩
  change ctx.G.degree left = input.minimumDegree ∨
    ctx.G.degree right = input.minimumDegree at critical
  rcases critical with leftTight | rightTight <;> omega

/-- Framework-owned outputs of the routed CT1-to-local-CT2 prefix for a
minimum-degree cycle target. -/
structure RoutedDeletionPrefix
    (input : StaticInput V BranchState)
    (encoding : CT1.TargetCertificateEncoding (P := input.problem)
      input.Target)
    (ctx : Core.MinimalCounterexampleContext input.problem input.Target) : Prop where
  ct1Terminal :
    ((input.certificateDeletionProfile encoding).runAvoiding ctx).result.terminal =
      .avoiding
  ct1Trace :
    ((input.certificateDeletionProfile encoding).runAvoiding ctx).result.trace =
      [.entry, .equivalenceCertification, .realizationDecision,
        .avoidingTerminal]
  transitionProfileId :
    ((input.certificateDeletionProfile encoding).transition ctx).profileId =
      Routes.CT1ToCT2.LocalDeletion.transitionId
  transitionNotEnabled : ∀ stage : Core.Routing.ResidualStage .ct2
    ((((input.certificateDeletionProfile encoding).transition ctx).onLedger
      ((input.certificateDeletionProfile encoding).currentAvoiding ctx)).EnabledStage
        ((input.certificateDeletionProfile encoding).sourceLedger ctx)),
    (input.certificateDeletionProfile encoding).outcome ctx ≠ .enabled stage
  dartHasTightEndpoint : ∀ dart : ctx.G.graph.Dart,
    ctx.G.degree dart.fst = input.minimumDegree ∨
      ctx.G.degree dart.snd = input.minimumDegree
  highDegreeIndependent : ∀ {left right : V},
    input.minimumDegree + 1 ≤ ctx.G.degree left →
    input.minimumDegree + 1 ≤ ctx.G.degree right →
      ¬ ctx.G.graph.Adj left right

/-- Construct the complete routed prefix on a supplied minimal context. -/
def routedDeletionPrefix
    (input : StaticInput V BranchState)
    (encoding : CT1.TargetCertificateEncoding (P := input.problem)
      input.Target)
    (ctx : Core.MinimalCounterexampleContext input.problem input.Target) :
    RoutedDeletionPrefix input encoding ctx where
  ct1Terminal :=
    ((input.certificateDeletionProfile encoding).runAvoiding ctx).terminal_eq
  ct1Trace :=
    ((input.certificateDeletionProfile encoding).runAvoiding ctx).trace_eq
  transitionProfileId := rfl
  transitionNotEnabled :=
    (input.certificateDeletionProfile encoding).transition_not_enabled ctx
  dartHasTightEndpoint := input.routedDart_has_tight_endpoint encoding ctx
  highDegreeIndependent := input.routedHighDegree_independent encoding ctx

/-- Natural-number well-ordering selects a rank-minimal counterexample and
executes the routed prefix without enumerating ambient graphs. -/
theorem exists_routedDeletionPrefix
    (input : StaticInput V BranchState)
    (encoding : CT1.TargetCertificateEncoding (P := input.problem)
      input.Target)
    (stateOf : (object : FiniteObject V) → BranchState object)
    (object : FiniteObject V) (baseline : input.problem.Baseline object)
    (avoids : ¬ input.Target object) :
    ∃ ctx : Core.MinimalCounterexampleContext input.problem input.Target,
      input.problem.rank ctx.G ≤ input.problem.rank object ∧
        RoutedDeletionPrefix input encoding ctx := by
  let initial : Core.AvoidingContext input.problem input.Target :=
    Core.AvoidingContext.ofBranch ⟨object, baseline, stateOf object⟩ avoids
  obtain ⟨ctx, rankLe⟩ :=
    initial.exists_minimalCounterexample stateOf
  exact ⟨ctx, rankLe, input.routedDeletionPrefix encoding ctx⟩

/-- Edge-rooted specialization of the routed prefix, including its exact
return-set avoidance theorem. -/
structure EdgeRootedDeletionPrefix
    (input : StaticInput V BranchState)
    (ctx : Core.MinimalCounterexampleContext input.problem input.Target) : Prop
    extends RoutedDeletionPrefix input input.edgeRootedEncoding ctx where
  returnSetsDisjoint : ∀ dart : ctx.G.graph.Dart,
    Disjoint (edgeReturnSet ctx.G.graph dart)
      {length | input.ReturnLengthOK length}

/-- Construct the edge-rooted routed prefix on a supplied minimal context. -/
def edgeRootedDeletionPrefix
    (input : StaticInput V BranchState)
    (ctx : Core.MinimalCounterexampleContext input.problem input.Target) :
    EdgeRootedDeletionPrefix input ctx where
  toRoutedDeletionPrefix :=
    input.routedDeletionPrefix input.edgeRootedEncoding ctx
  returnSetsDisjoint :=
    (input.not_target_iff_returnSets_disjoint ctx.G).mp ctx.avoids

/-- Select a rank-minimal counterexample and execute the complete edge-rooted
CT1-to-local-CT2 prefix. -/
theorem exists_edgeRootedDeletionPrefix
    (input : StaticInput V BranchState)
    (stateOf : (object : FiniteObject V) → BranchState object)
    (object : FiniteObject V) (baseline : input.problem.Baseline object)
    (avoids : ¬ input.Target object) :
    ∃ ctx : Core.MinimalCounterexampleContext input.problem input.Target,
      input.problem.rank ctx.G ≤ input.problem.rank object ∧
        EdgeRootedDeletionPrefix input ctx := by
  obtain ⟨ctx, rankLe, _prefix⟩ := input.exists_routedDeletionPrefix
    input.edgeRootedEncoding stateOf object baseline avoids
  exact ⟨ctx, rankLe, input.edgeRootedDeletionPrefix ctx⟩

end StructuralExhaustion.Graph.MinimumDegreeCycle.StaticInput
