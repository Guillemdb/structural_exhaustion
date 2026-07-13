import Erdos64EG.CT10P13LabelAlgebra

namespace Erdos64EG.Tests

open StructuralExhaustion
open StructuralExhaustion.Graph
open Erdos64EG.Internal

/-!
Small executable smoke fixture for the first slice.  `K₄` satisfies the
official baseline and contains the explicitly certified four-cycle below, so
the generated CT1 machine is forced to its C1 terminal.
-/

def k4 : Object (Fin 4) where
  graph := ⊤
  input := {
    vertices := inferInstance
    decideAdj := inferInstance
  }

theorem k4_baseline : Baseline k4 := by
  change 3 ≤ (⊤ : SimpleGraph (Fin 4)).minDegree
  simp

def fourCycleWalk : k4.graph.Walk (0 : Fin 4) 0 :=
  letI : DecidableRel k4.graph.Adj := k4.input.decideAdj
  .cons (show k4.graph.Adj 0 1 by decide) <|
    .cons (show k4.graph.Adj 1 2 by decide) <|
      .cons (show k4.graph.Adj 2 3 by decide) <|
        .cons (show k4.graph.Adj 3 0 by decide) .nil

theorem fourCycleWalk_isCycle : fourCycleWalk.IsCycle := by
  rw [SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length]
  constructor
  · rw [SimpleGraph.Walk.isPath_def]
    decide
  · decide

theorem fourCycleWalk_powerOfTwo :
    PowerOfTwoLength fourCycleWalk.length := by
  change PowerOfTwoLength 4
  exact ⟨⟨2, by decide⟩, by decide, rfl⟩

def k4Cycle : CycleWithLength k4.graph PowerOfTwoLength :=
  {
    vertex := 0
    walk := fourCycleWalk
    isCycle := fourCycleWalk_isCycle
    length_ok := fourCycleWalk_powerOfTwo
  }

def k4Target : Target k4 := ⟨k4Cycle⟩

/-- The manuscript conversion deletes the first edge of the four-cycle and
produces the length-three Mersenne return in `K₄ - e`. -/
def k4MersenneReturn : MersenneReturn k4.graph :=
  EdgeRootedReturn.ofCycle k4Cycle

example : k4MersenneReturn.path.length = 3 := rfl

example : MersenneLength 3 := by
  exact (mersenneLength_iff 3).mpr ⟨2, by decide, rfl⟩

/-- End-to-end local validation of the explicit cycle certificate. -/
def k4CT1Run :
    StructuralExhaustion.CT1.CertifiedC1Run
      (ct1Spec (Fin 4)) (ct1Input k4 k4_baseline) :=
  runCT1 k4 k4_baseline k4Cycle

def k4MersenneCT1Run :
    StructuralExhaustion.CT1.CertifiedC1Run
      (ct1Spec (Fin 4)) (ct1Input k4 k4_baseline) :=
  runMersenneCT1 k4 k4_baseline k4MersenneReturn

example : k4MersenneCT1Run.result.terminal = .c1 :=
  k4MersenneCT1Run.terminal_eq

example : k4MersenneCT1Run.result.trace =
    [.entry, .equivalenceCertification, .realizationDecision, .c1Terminal] :=
  k4MersenneCT1Run.trace_eq

example : k4MersenneCT1Run.checks = 1 :=
  k4MersenneCT1Run.checks_eq

/-! Type-level regression coverage for manuscript node [8].  A retained
minimum-degree-three proper core executes the exact CT2 closure path, while
the exported theorem rules that branch out. -/

universe u

variable
  (ctx : StructuralExhaustion.Core.MinimalCounterexampleContext
    (Graph.PackedMinimumDegreeCycle.StaticInput.problem.{u}
      packedStaticInput)
    (Graph.PackedMinimumDegreeCycle.StaticInput.Target.{u}
      packedStaticInput))
  (subgraph : Graph.PackedFiniteObject.ProperSubgraph ctx.G)
  (minimumDegreeThree : 3 ≤ subgraph.value.object.minDegree)

example : (properCoreCT2Run ctx subgraph minimumDegreeThree).terminal =
    .deletionC2 :=
  properCoreCT2Run_terminal ctx subgraph minimumDegreeThree

example : (properCoreCT2Run ctx subgraph minimumDegreeThree).trace =
    [.entry, .deletionDecision, .deletionC2Terminal] :=
  properCoreCT2Run_trace ctx subgraph minimumDegreeThree

example : (properCoreCT2Run ctx subgraph minimumDegreeThree).checks = 1 :=
  properCoreCT2Run_checks ctx subgraph minimumDegreeThree

example : subgraph.value.object.minDegree ≤ 2 :=
  properSubgraph_minDegree_le_two ctx subgraph

/-! Type-level regression coverage for the single CT3 stage spanning diagram
nodes [11]--[14].  The replacement is proof-specified, so the runner performs
one local certificate check and the exported theorem rules out the branch. -/

variable (verifiedPrefix : VerifiedBoundariedReplacementPrefix ctx)

example : VerifiedNoProperCorePrefix ctx :=
  boundariedReplacementPrefix_previous ctx verifiedPrefix

variable
  (TConcrete : Type u)
  (concreteBoundaries : FinEnum TConcrete)
  [Nonempty TConcrete]
  (concreteAtom : ConcreteCT3.ProperAtom ctx concreteBoundaries)
  (concreteCompression : ConcreteCT3.Compression concreteAtom)

example : (Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.Compression.run
    concreteCompression).terminal = .compression :=
  concreteCompression.run_terminal

example : (Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.Compression.run
    concreteCompression).trace =
      [.entry, .vectorComputation, .compressionSearch,
        .compressionTerminal] :=
  concreteCompression.run_trace

example : (Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.Compression.run
    concreteCompression).checks = 1 :=
  concreteCompression.run_checks

example :
    (Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement.Compression.run
      concreteCompression).checks ≤
      (CT3.certifiedCompressionBudget ctx).coefficient *
        ((CT3.certifiedCompressionBudget ctx).size
            concreteCompression.certifiedInput + 1) ^
          (CT3.certifiedCompressionBudget ctx).degree :=
  concreteCompression.run_polynomial

example : ∃ result : CT3.CertifiedCompressionRun ctx
      concreteCompression.certifiedInput,
    result.terminal = .compression ∧
      result.trace = [.entry, .vectorComputation, .compressionSearch,
        .compressionTerminal] :=
  concreteCompression.run_total

example : False := concreteCompression.impossible

example : False :=
  boundariedReplacementPrefix_uncompressible ctx verifiedPrefix
    concreteBoundaries concreteAtom concreteCompression

/-! Type-level regression coverage for the next single CT1 stage spanning
diagram nodes `[15]`--`[16]`.  The avoiding path is closed by the sole HSS
external theorem, and the forced induced-path certificate follows the exact
C1 path with one local validation check. -/

variable
  (p13Free : P13Free ctx)
  (p13Certificate : InducedP13Certificate ctx)

example : (runP13FreeCT1 ctx p13Free).result.terminal = .avoiding :=
  runP13FreeCT1_terminal ctx p13Free

example : (runP13FreeCT1 ctx p13Free).result.trace =
    [.entry, .equivalenceCertification, .realizationDecision,
      .avoidingTerminal] :=
  runP13FreeCT1_trace ctx p13Free

example : (runP13FreeCT1 ctx p13Free).checks = 0 :=
  runP13FreeCT1_checks ctx p13Free

example : False :=
  p13FreeBranch_closed ctx p13Free

example : HasInducedP13 ctx :=
  inducedP13_of_hss ctx

example : (runInducedP13CT1 ctx p13Certificate).result.terminal = .c1 :=
  runInducedP13CT1_terminal ctx p13Certificate

example : (runInducedP13CT1 ctx p13Certificate).result.trace =
    [.entry, .equivalenceCertification, .realizationDecision,
      .c1Terminal] :=
  runInducedP13CT1_trace ctx p13Certificate

example : (runInducedP13CT1 ctx p13Certificate).checks = 1 :=
  runInducedP13CT1_checks ctx p13Certificate

variable (p13Prefix : VerifiedInducedP13Prefix ctx)

example : VerifiedBoundariedReplacementPrefix ctx :=
  inducedP13Prefix_previous ctx p13Prefix

example : packedStaticInput.VerifiedInducedPathStage 13 ctx :=
  inducedP13Prefix_stage ctx p13Prefix

example : HasInducedP13 ctx :=
  inducedP13Prefix_realization ctx p13Prefix

/-! The next composed prefix consumes that exact CT1 output and retains the
maximum/maximal packing, CT12 audit, induced-`P₁₃`-free remainder, and no
internal three-core consequence. -/

variable (packingPrefix : VerifiedP13PackingPrefix ctx)

example : VerifiedInducedP13Prefix ctx :=
  p13PackingPrefix_previous ctx packingPrefix

example : Graph.InducedPathPacking.VerifiedStage ctx.G.object 13
    (by decide) ctx.toBranchContext :=
  p13PackingPrefix_stage ctx packingPrefix

example : p13Windows ctx ≠ [] :=
  p13PackingPrefix_nonempty ctx packingPrefix

example : (runP13PackingCT12 ctx).terminal = .exhausted :=
  runP13PackingCT12_terminal ctx

example : (runP13PackingCT12 ctx).iterations ≤
    ctx.G.object.input.vertices.card :=
  runP13PackingCT12_iterations ctx

example : (runP13PackingCT12 ctx).iterations = p13 ctx :=
  runP13PackingCT12_iterations_exact ctx

example : (p13RemainderVertices ctx).card + 13 * p13 ctx =
    ctx.G.object.input.vertices.card :=
  p13Remainder_partition ctx

example : Graph.InducedPathFree (p13Remainder ctx).graph 13 :=
  p13Remainder_free ctx

example : (p13Remainder ctx).InternalMinDegreeFree 3 :=
  packingPrefix.noInternalThreeCore

example : ¬(p13Remainder ctx).HasInternalSubgraphMinDegreeAtLeast 3 :=
  packingPrefix.noInternalSubgraphThreeCore

/-! Node `[18]` consumes that exact CT12 prefix.  CT10 exhausts the compact
`P₁₃` label universe, while the graph layer proves that every actual
attachment in the selected target-avoiding graph enters the accepted table. -/

variable (labelPrefix : VerifiedP13LabelAlgebraPrefix ctx)

example : VerifiedP13PackingPrefix ctx :=
  p13LabelAlgebraPrefix_previous ctx labelPrefix

example : p13LabelClassification.VerifiedStage ctx.toBranchContext :=
  p13LabelAlgebraPrefix_stage ctx labelPrefix

example : p13LabelClassification.candidateCount = 8192 :=
  p13Label_candidate_count

example : p13LabelClassification.classCount = 399 :=
  p13LegalLabel_count

example : p13LabelClassification.checks = 167792 :=
  p13Label_check_count

example : p13LabelClassification.checks ≤
    (p13LabelClassification.candidateCount + 1) ^ 2 :=
  p13Label_checks_quadratic

example : (runP13LabelCT10 ctx).terminal = .exhaustive :=
  runP13LabelCT10_terminal ctx

example : (runP13LabelCT10 ctx).trace =
    [.entry, .table, .direct, .missing, .exhaustiveTerminal] :=
  runP13LabelCT10_trace ctx

example : ∃ result : CT10.ExecutionResult
    (p13LabelClassification.capability PackedProblem.{u})
    (p13LabelCT10Input ctx),
    result.terminal = .exhaustive ∧
      result.trace =
        [.entry, .table, .direct, .missing, .exhaustiveTerminal] ∧
      result.outcome.Valid ∧
      CT10.Graph.ValidTrace
        (p13LabelClassification.capability PackedProblem.{u})
        (p13LabelCT10Input ctx) result.trace :=
  runP13LabelCT10_total ctx

variable
  (path : SimpleGraph.pathGraph 13 ↪g ctx.G.object.graph)
  (outside : ctx.G.Vertex)
  (outsidePath : ∀ position : Fin 13, outside ≠ path position)
  (attached : ∃ position, ctx.G.object.graph.Adj outside (path position))

example : P13Legal
    (packedStaticInput.inducedPathAttachmentLabel 13 ctx path outside) :=
  p13AttachmentLabel_legal ctx labelPrefix path outside outsidePath attached

example : p13LabelClassification.Accepts
    (p13LabelEquiv.symm
      (packedStaticInput.inducedPathAttachmentLabel 13 ctx path outside)) :=
  p13AttachmentLabel_accepted ctx labelPrefix path outside outsidePath attached

end Erdos64EG.Tests
