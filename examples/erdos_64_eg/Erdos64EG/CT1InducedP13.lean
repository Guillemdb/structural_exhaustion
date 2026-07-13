import Erdos64EG.CT3
import StructuralExhaustion.Graph.External.HegdeSandeepShashank

namespace Erdos64EG.Internal

open StructuralExhaustion

universe u

/-!
# CT1: the induced-P₁₃ branch

One CT1 stage realizes manuscript nodes `[15]` and `[16]` together.  CT1's
realization is a literal Mathlib embedding of `pathGraph 13`, hence an induced
path with thirteen distinct vertices and no chords.  Its avoiding residual is
exactly `P₁₃`-freeness.  The Hegde--Sandeep--Shashank theorem closes that
residual against the already verified dyadic-target avoidance, forcing a
certificate-driven C1 execution.
-/

/-- The induced-path CT1 profile on the exact packed problem selected by the
preceding prefix. -/
abbrev inducedP13Profile := packedStaticInput.inducedPathProfile 13

/-- CT1 input retaining the selected packed branch context definitionally. -/
abbrev inducedP13Input
    (ctx : Core.MinimalCounterexampleContext PackedProblem PackedTarget) :=
  packedStaticInput.inducedPathInput ctx

/-- One proof-carrying induced copy of `P₁₃`. -/
abbrev InducedP13Certificate
    (ctx : Core.MinimalCounterexampleContext PackedProblem PackedTarget) :=
  packedStaticInput.InducedPathCertificate 13 ctx

/-- Literal manuscript proposition that the selected graph contains an
induced path on thirteen vertices. -/
abbrev HasInducedP13
    (ctx : Core.MinimalCounterexampleContext PackedProblem PackedTarget) :=
  Graph.HasInducedPath ctx.G.object.graph 13

/-- Literal manuscript proposition that the selected graph is `P₁₃`-free. -/
abbrev P13Free
    (ctx : Core.MinimalCounterexampleContext PackedProblem PackedTarget) :=
  Graph.InducedPathFree ctx.G.object.graph 13

/-! ## Nodes [15] and [16]: avoiding branch and HSS closure -/

/-- Exact CT1 avoiding execution produced by the `P₁₃`-free branch test. -/
def runP13FreeCT1
    (ctx : Core.MinimalCounterexampleContext PackedProblem PackedTarget)
    (free : P13Free ctx) :=
  inducedP13Profile.runAvoiding (inducedP13Input ctx) free

theorem runP13FreeCT1_terminal
    (ctx : Core.MinimalCounterexampleContext PackedProblem PackedTarget)
    (free : P13Free ctx) :
    (runP13FreeCT1 ctx free).result.terminal = .avoiding :=
  inducedP13Profile.runAvoiding_terminal (inducedP13Input ctx) free

theorem runP13FreeCT1_trace
    (ctx : Core.MinimalCounterexampleContext PackedProblem PackedTarget)
    (free : P13Free ctx) :
    (runP13FreeCT1 ctx free).result.trace =
      [.entry, .equivalenceCertification, .realizationDecision,
        .avoidingTerminal] :=
  inducedP13Profile.runAvoiding_trace (inducedP13Input ctx) free

theorem runP13FreeCT1_total
    (ctx : Core.MinimalCounterexampleContext PackedProblem PackedTarget)
    (free : P13Free ctx) :
    ∃ run : CT1.CertifiedAvoidingRun inducedP13Profile.encoding.spec
        (inducedP13Input ctx),
      run.result.terminal = .avoiding ∧
        run.result.trace =
          [.entry, .equivalenceCertification, .realizationDecision,
            .avoidingTerminal] :=
  inducedP13Profile.runAvoiding_total (inducedP13Input ctx) free

theorem runP13FreeCT1_checks
    (ctx : Core.MinimalCounterexampleContext PackedProblem PackedTarget)
    (free : P13Free ctx) :
    (runP13FreeCT1 ctx free).checks = 0 :=
  inducedP13Profile.runAvoiding_checks (inducedP13Input ctx) free

theorem runP13FreeCT1_polynomial
    (ctx : Core.MinimalCounterexampleContext PackedProblem PackedTarget)
    (free : P13Free ctx) :
    (runP13FreeCT1 ctx free).checks ≤
      (CT1.certifiedAvoidingBudget inducedP13Profile.encoding.spec).coefficient *
        ((CT1.certifiedAvoidingBudget
            inducedP13Profile.encoding.spec).size (inducedP13Input ctx) + 1) ^
          (CT1.certifiedAvoidingBudget
            inducedP13Profile.encoding.spec).degree :=
  inducedP13Profile.runAvoiding_polynomial (inducedP13Input ctx) free

/-- The sole external HSS theorem translates a `P₁₃`-free selected graph into
the exact packed dyadic-cycle target. -/
theorem hssTarget_of_p13Free
    (ctx : Core.MinimalCounterexampleContext PackedProblem PackedTarget)
    (free : P13Free ctx) : PackedTarget ctx.G := by
  letI : FinEnum ctx.G.Vertex := ctx.G.object.input.vertices
  letI : DecidableRel ctx.G.object.graph.Adj :=
    ctx.G.object.input.decideAdj
  rcases
      Graph.External.HegdeSandeepShashank.p13Free_hasPowerOfTwoCycle
        ctx.G.object.graph ctx.baseline free with
    certificate
  exact target_of_unboundedPowerOfTwoCycle ctx.G.object certificate

/-- Node `[16]`: the actual CT1 avoiding residual is impossible because HSS
would produce the target already excluded by the selected context. -/
theorem p13FreeBranch_closed
    (ctx : Core.MinimalCounterexampleContext PackedProblem PackedTarget)
    (free : P13Free ctx) : False := by
  have verifiedFree : P13Free ctx :=
    inducedP13Profile.runAvoiding_verified (inducedP13Input ctx) free
  exact ctx.avoids (hssTarget_of_p13Free ctx verifiedFree)

/-- Corollary `cor:p13-exists`: every selected counterexample contains an
induced `P₁₃`. -/
theorem inducedP13_of_hss
    (ctx : Core.MinimalCounterexampleContext PackedProblem PackedTarget) :
    HasInducedP13 ctx := by
  by_contra free
  exact p13FreeBranch_closed ctx free

/-! ## Forced realization branch -/

/-- Exact certificate-driven CT1 run on one induced `P₁₃` embedding. -/
def runInducedP13CT1
    (ctx : Core.MinimalCounterexampleContext PackedProblem PackedTarget)
    (certificate : InducedP13Certificate ctx) :=
  packedStaticInput.inducedPathRun 13 ctx certificate

theorem runInducedP13CT1_terminal
    (ctx : Core.MinimalCounterexampleContext PackedProblem PackedTarget)
    (certificate : InducedP13Certificate ctx) :
    (runInducedP13CT1 ctx certificate).result.terminal = .c1 :=
  inducedP13Profile.run_terminal (inducedP13Input ctx) certificate

theorem runInducedP13CT1_trace
    (ctx : Core.MinimalCounterexampleContext PackedProblem PackedTarget)
    (certificate : InducedP13Certificate ctx) :
    (runInducedP13CT1 ctx certificate).result.trace =
      [.entry, .equivalenceCertification, .realizationDecision,
        .c1Terminal] :=
  inducedP13Profile.run_trace (inducedP13Input ctx) certificate

theorem runInducedP13CT1_verified
    (ctx : Core.MinimalCounterexampleContext PackedProblem PackedTarget)
    (certificate : InducedP13Certificate ctx) :
    HasInducedP13 ctx :=
  inducedP13Profile.run_verified (inducedP13Input ctx) certificate

theorem runInducedP13CT1_total
    (ctx : Core.MinimalCounterexampleContext PackedProblem PackedTarget)
    (certificate : InducedP13Certificate ctx) :
    ∃ run : CT1.CertifiedC1Run inducedP13Profile.encoding.spec
        (inducedP13Input ctx),
      run.result.terminal = .c1 ∧
        run.result.trace =
          [.entry, .equivalenceCertification, .realizationDecision,
            .c1Terminal] :=
  inducedP13Profile.run_total (inducedP13Input ctx) certificate

theorem runInducedP13CT1_checks
    (ctx : Core.MinimalCounterexampleContext PackedProblem PackedTarget)
    (certificate : InducedP13Certificate ctx) :
    (runInducedP13CT1 ctx certificate).checks = 1 :=
  inducedP13Profile.run_checks (inducedP13Input ctx) certificate

theorem runInducedP13CT1_polynomial
    (ctx : Core.MinimalCounterexampleContext PackedProblem PackedTarget)
    (certificate : InducedP13Certificate ctx) :
    (runInducedP13CT1 ctx certificate).checks ≤
      (CT1.certifiedC1Budget inducedP13Profile.encoding.spec).coefficient *
        ((CT1.certifiedC1Budget
            inducedP13Profile.encoding.spec).size (inducedP13Input ctx) + 1) ^
          (CT1.certifiedC1Budget inducedP13Profile.encoding.spec).degree :=
  inducedP13Profile.run_polynomial (inducedP13Input ctx) certificate

/-- Complete CT1 stage forced by HSS, including an existentially retained
positive execution with its terminal, trace, semantics, totality, and budget. -/
def verifiedInducedP13Stage
    (ctx : Core.MinimalCounterexampleContext PackedProblem PackedTarget) :
    packedStaticInput.VerifiedInducedPathStage 13 ctx :=
  packedStaticInput.verifiedInducedPathStage 13 ctx (inducedP13_of_hss ctx)

/-! ## Completed verified prefix -/

/-- Exact output of manuscript nodes `[15]`--`[16]`, retaining the authoritative
concrete CT3 result on the same packed minimal context. -/
structure VerifiedInducedP13Prefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem PackedTarget) : Prop where
  previous : VerifiedBoundariedReplacementPrefix ctx
  inducedPathStage : packedStaticInput.VerifiedInducedPathStage 13 ctx

/-- Extend the exact preceding prefix with the HSS-forced CT1 realization. -/
def verifiedInducedP13Prefix
    (ctx : Core.MinimalCounterexampleContext PackedProblem PackedTarget)
    (previous : VerifiedBoundariedReplacementPrefix ctx) :
    VerifiedInducedP13Prefix ctx where
  previous := previous
  inducedPathStage := packedStaticInput.verifiedInducedPathStage 13 ctx
    (inducedP13_of_hss ctx)

/-- Provenance: the new CT1 stage retains the exact CT3 prefix it consumes. -/
theorem inducedP13Prefix_previous
    (ctx : Core.MinimalCounterexampleContext PackedProblem PackedTarget)
    (verified : VerifiedInducedP13Prefix ctx) :
    VerifiedBoundariedReplacementPrefix ctx :=
  verified.previous

/-- The composed prefix contains the complete induced-path CT1 execution. -/
theorem inducedP13Prefix_stage
    (ctx : Core.MinimalCounterexampleContext PackedProblem PackedTarget)
    (verified : VerifiedInducedP13Prefix ctx) :
    packedStaticInput.VerifiedInducedPathStage 13 ctx :=
  verified.inducedPathStage

/-- Concrete manuscript consequence retained by the composed prefix. -/
theorem inducedP13Prefix_realization
    (ctx : Core.MinimalCounterexampleContext PackedProblem PackedTarget)
    (verified : VerifiedInducedP13Prefix ctx) :
    HasInducedP13 ctx :=
  verified.inducedPathStage.realization

/-- Starting only from the official internal counterexample data, retain the
same lexicographically selected graph and extend the verified proof through
the complete nodes `[15]`--`[16]` CT1 block. -/
theorem exists_verifiedInducedP13Prefix {V : Type u}
    (object : Object V) (baseline : Baseline object)
    (avoids : ¬ Target object) :
    ∃ ctx : Core.MinimalCounterexampleContext
        (Graph.PackedMinimumDegreeCycle.StaticInput.problem.{u}
          packedStaticInput)
        (Graph.PackedMinimumDegreeCycle.StaticInput.Target.{u}
          packedStaticInput),
      (Graph.PackedMinimumDegreeCycle.StaticInput.problem.{u}
        packedStaticInput).rank ctx.G ≤
          (Graph.PackedMinimumDegreeCycle.StaticInput.problem.{u}
            packedStaticInput).rank
            (Graph.PackedFiniteObject.pack object) ∧
        VerifiedInducedP13Prefix ctx := by
  obtain ⟨ctx, rankLe, previous⟩ :=
    exists_verifiedBoundariedReplacementPrefix object baseline avoids
  exact ⟨ctx, rankLe, verifiedInducedP13Prefix ctx previous⟩

end Erdos64EG.Internal
