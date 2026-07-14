import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic
import StructuralExhaustion.CT2.CertifiedReduction
import StructuralExhaustion.Graph.InducedPath
import StructuralExhaustion.Graph.InducedPathAttachment
import StructuralExhaustion.Graph.InducedPathPacking
import StructuralExhaustion.Graph.MinimumDegreeCycleRouted
import StructuralExhaustion.Routes.CT1ToCT12

namespace StructuralExhaustion.Graph

open StructuralExhaustion

universe u v

/-!
# Lexicographically minimal finite cycle counterexamples

`PackedFiniteObject` permits one `Core.Problem` to compare finite graphs whose
vertex types differ.  Its natural-number rank encodes the manuscript order
first by vertex count and then by edge count.  Selection is proof-level
well-ordering; neither this module nor its CT2 profile enumerates graphs or
subgraphs.
-/

/-- A finite Mathlib graph with its vertex type hidden in the ambient object. -/
structure PackedFiniteObject where
  Vertex : Type u
  object : FiniteObject Vertex

namespace PackedFiniteObject

/-- Pack an ordinary finite graph without changing any graph data. -/
def pack {V : Type u} (object : FiniteObject V) : PackedFiniteObject.{u} :=
  ⟨V, object⟩

/-- Number of vertices in the declared finite inspection order. -/
def vertexCount (packed : PackedFiniteObject.{u}) : Nat :=
  packed.object.input.vertices.card

/-- Number of Mathlib edges in the packed graph. -/
def edgeCount (packed : PackedFiniteObject.{u}) : Nat :=
  packed.object.edgeCount

/-- A natural-number encoding of lexicographic `(vertices, edges)` order on
finite simple graphs.  Cubic vertex bands dominate the at-most-quadratic edge
count in every preceding band. -/
def lexRank (packed : PackedFiniteObject.{u}) : Nat :=
  packed.vertexCount ^ 3 + packed.edgeCount

@[simp] theorem vertexCount_pack {V : Type u} (object : FiniteObject V) :
    (pack object).vertexCount = object.input.vertices.card := rfl

@[simp] theorem edgeCount_pack {V : Type u} (object : FiniteObject V) :
    (pack object).edgeCount = object.edgeCount := rfl

@[simp] theorem lexRank_pack {V : Type u} (object : FiniteObject V) :
    (pack object).lexRank =
      object.input.vertices.card ^ 3 + object.edgeCount := rfl

/-- A finite simple graph has at most the square of its vertex count many
edges. -/
theorem edgeCount_le_vertexCount_sq (packed : PackedFiniteObject.{u}) :
    packed.edgeCount ≤ packed.vertexCount ^ 2 := by
  letI : FinEnum packed.Vertex := packed.object.input.vertices
  letI : DecidableRel packed.object.graph.Adj :=
    packed.object.input.decideAdj
  have edgeBound : packed.object.graph.edgeFinset.card ≤
      (Fintype.card packed.Vertex).choose 2 :=
    SimpleGraph.card_edgeFinset_le_card_choose_two
  have chooseBound : (Fintype.card packed.Vertex).choose 2 ≤
      Fintype.card packed.Vertex ^ 2 :=
    Nat.choose_le_pow _ _
  simpa [edgeCount, vertexCount, FiniteObject.edgeCount,
    FinEnum.card_eq_fintypeCard] using edgeBound.trans chooseBound

/-- Strictly fewer vertices force a smaller encoded lexicographic rank. -/
theorem lexRank_lt_of_vertexCount_lt
    {smaller larger : PackedFiniteObject.{u}}
    (countLt : smaller.vertexCount < larger.vertexCount) :
    smaller.lexRank < larger.lexRank := by
  have edgesLe : smaller.edgeCount ≤ smaller.vertexCount ^ 2 :=
    smaller.edgeCount_le_vertexCount_sq
  calc
    smaller.lexRank =
        smaller.vertexCount ^ 3 + smaller.edgeCount := rfl
    _ ≤ smaller.vertexCount ^ 3 + smaller.vertexCount ^ 2 :=
      Nat.add_le_add_left edgesLe _
    _ < (smaller.vertexCount + 1) ^ 3 := by nlinarith
    _ ≤ larger.vertexCount ^ 3 := by
      exact Nat.pow_le_pow_left (Nat.succ_le_iff.mpr countLt) 3
    _ ≤ larger.vertexCount ^ 3 + larger.edgeCount :=
      Nat.le_add_right _ _
    _ = larger.lexRank := rfl

/-- With vertex count fixed, fewer edges force a smaller encoded
lexicographic rank. -/
theorem lexRank_lt_of_vertexCount_eq_edgeCount_lt
    {smaller larger : PackedFiniteObject.{u}}
    (countEq : smaller.vertexCount = larger.vertexCount)
    (edgesLt : smaller.edgeCount < larger.edgeCount) :
    smaller.lexRank < larger.lexRank := by
  unfold lexRank
  rw [countEq]
  exact Nat.add_lt_add_left edgesLt _

/-- A graph-local certificate that `value` is a proper subgraph of `source`.
The embedding and inclusion are the mathematical subgraph relation; `strict`
records its lexicographic properness. -/
structure ProperSubgraph (source : PackedFiniteObject.{u}) where
  value : PackedFiniteObject.{u}
  vertexEmbedding : value.Vertex ↪ source.Vertex
  included : value.object.graph.map vertexEmbedding ≤ source.object.graph
  strict : value.vertexCount < source.vertexCount ∨
    (value.vertexCount = source.vertexCount ∧
      value.edgeCount < source.edgeCount)

namespace ProperSubgraph

/-- A twice-induced graph on a support strictly smaller than the source is a
proper packed subgraph of that source. -/
def ofInducedCore (source : PackedFiniteObject.{u})
    (support : Finset source.Vertex)
    (supportStrict : support.card < source.vertexCount)
    (core : Finset {vertex : source.Vertex // vertex ∈ support}) :
    ProperSubgraph source where
  value := pack ((source.object.induceFinset support).induceFinset core)
  vertexEmbedding := ⟨fun vertex => vertex.1.1, by
    intro left right equal
    apply Subtype.ext
    apply Subtype.ext
    exact equal⟩
  included := by
    rintro left right ⟨_ne, innerLeft, innerRight, adjacent, rfl, rfl⟩
    exact adjacent
  strict := by
    left
    simp only [vertexCount_pack, FiniteObject.induceFinset_vertexCount]
    calc
      core.card ≤ Fintype.card {vertex : source.Vertex // vertex ∈ support} :=
        Finset.card_le_univ core
      _ = support.card := Fintype.card_coe support
      _ < source.vertexCount := supportStrict

/-- A proper induced support inherits minimum-degree-core freeness from a
packed no-proper-core theorem. -/
theorem internalMinDegreeFree_induceFinset_of_noProperCore
    (source : PackedFiniteObject.{u}) (bound : Nat)
    (support : Finset source.Vertex)
    (supportStrict : support.card < source.vertexCount)
    (noProperCore : ∀ subgraph : ProperSubgraph source,
      ¬ bound ≤ subgraph.value.object.minDegree) :
    (source.object.induceFinset support).InternalMinDegreeFree bound := by
  rintro ⟨core, minimumDegree⟩
  exact noProperCore (ofInducedCore source support supportStrict core)
    minimumDegree

/-- The injective graph homomorphism underlying a proper-subgraph
certificate. -/
def hom {source : PackedFiniteObject.{u}}
    (subgraph : ProperSubgraph source) :
    subgraph.value.object.graph →g source.object.graph where
  toFun := subgraph.vertexEmbedding
  map_rel' := by
    intro left right adjacent
    exact subgraph.included
      ((SimpleGraph.map_adj_apply).2 adjacent)

theorem hom_injective {source : PackedFiniteObject.{u}}
    (subgraph : ProperSubgraph source) :
    Function.Injective subgraph.hom :=
  subgraph.vertexEmbedding.injective

/-- Proper-subgraph certificates strictly decrease the packed problem rank. -/
theorem lexRank_lt {source : PackedFiniteObject.{u}}
    (subgraph : ProperSubgraph source) :
    subgraph.value.lexRank < source.lexRank := by
  rcases subgraph.strict with countLt | ⟨countEq, edgesLt⟩
  · exact lexRank_lt_of_vertexCount_lt countLt
  · exact lexRank_lt_of_vertexCount_eq_edgeCount_lt countEq edgesLt

/-- Every accepted cycle in a proper subgraph maps to an accepted cycle of
the source with exactly the same length. -/
theorem hasCycleWithLength_mono {source : PackedFiniteObject.{u}}
    (subgraph : ProperSubgraph source) {LengthOK : Nat → Prop} :
    HasCycleWithLength subgraph.value.object.graph LengthOK →
      HasCycleWithLength source.object.graph LengthOK :=
  hasCycleWithLength_mapHom subgraph.hom subgraph.hom_injective

end ProperSubgraph

end PackedFiniteObject

namespace PackedMinimumDegreeCycle

/-- Problem-independent parameters for a lexicographically minimal finite
minimum-degree cycle counterexample. -/
structure StaticInput where
  minimumDegree : Nat
  LengthOK : Nat → Prop

namespace StaticInput

/-- The existing fixed-vertex graph profile obtained by exposing a packed
object's vertex type. -/
def fixed (input : StaticInput) (V : Type u) :
    MinimumDegreeCycle.StaticInput V (fun _object => Unit) where
  minimumDegree := input.minimumDegree
  LengthOK := input.LengthOK

/-- Public cycle target on a packed graph. -/
def Target (input : StaticInput) (packed : PackedFiniteObject.{u}) : Prop :=
  HasCycleWithLength packed.object.graph input.LengthOK

/-- Shared packed problem with minimum-degree baseline and lexicographic
vertex/edge rank. -/
def problem (input : StaticInput) : Core.Problem.{u + 1, 0} where
  Ambient := PackedFiniteObject.{u}
  Baseline := fun packed => input.minimumDegree ≤ packed.object.minDegree
  rank := PackedFiniteObject.lexRank
  BranchState := fun _packed => Unit

/-- The packed target agrees definitionally with the established fixed-vertex
cycle target. -/
theorem target_eq_fixed (input : StaticInput)
    (packed : PackedFiniteObject.{u}) :
    input.Target packed = (input.fixed packed.Vertex).Target packed.object :=
  rfl

/-- A packed minimal context induces the fixed-vertex edge-minimal context
consumed by the existing edge-rooted CT1 and dart-deletion CT2 profiles. -/
def fixedContext (input : StaticInput)
    (ctx : Core.MinimalCounterexampleContext input.problem input.Target) :
    Core.MinimalCounterexampleContext
      (input.fixed ctx.G.Vertex).problem
      (input.fixed ctx.G.Vertex).Target where
  toAvoidingContext := {
    toBranchContext := {
      G := ctx.G.object
      baseline := ctx.baseline
      state := ()
    }
    avoids := ctx.avoids
  }
  minimal := by
    intro object smaller baseline
    apply ctx.minimal (PackedFiniteObject.pack object)
    · change object.edgeCount < ctx.G.object.edgeCount at smaller
      apply PackedFiniteObject.lexRank_lt_of_vertexCount_eq_edgeCount_lt
      · exact FinEnum.card_unique object.input.vertices
          ctx.G.object.input.vertices
      · exact smaller
    · exact baseline

/-- Turn one explicit proper subgraph retaining the baseline into the exact
certificate-driven CT2 input. -/
def properSubgraphCT2Input (input : StaticInput)
    (ctx : Core.MinimalCounterexampleContext input.problem input.Target)
    (subgraph : PackedFiniteObject.ProperSubgraph ctx.G)
    (baseline : input.problem.Baseline subgraph.value) :
    CT2.CertifiedReductionInput ctx where
  reduction := {
    value := subgraph.value
    decreases := subgraph.lexRank_lt
  }
  reducedBaseline := baseline
  targetMonotone := subgraph.hasCycleWithLength_mono

/-- Execute the canonical deletion-C2 path for an explicitly supplied proper
subgraph that is assumed to retain the baseline. -/
def properSubgraphCT2Run (input : StaticInput)
    (ctx : Core.MinimalCounterexampleContext input.problem input.Target)
    (subgraph : PackedFiniteObject.ProperSubgraph ctx.G)
    (baseline : input.problem.Baseline subgraph.value) :
    CT2.CertifiedReductionRun ctx
      (input.properSubgraphCT2Input ctx subgraph baseline) :=
  CT2.runCertifiedReduction ctx
    (input.properSubgraphCT2Input ctx subgraph baseline)

/-- No proper subgraph of a lexicographically minimal counterexample retains
the minimum-degree baseline. -/
theorem noProperCore (input : StaticInput)
    (ctx : Core.MinimalCounterexampleContext input.problem input.Target)
    (subgraph : PackedFiniteObject.ProperSubgraph ctx.G) :
    ¬ input.problem.Baseline subgraph.value := by
  intro baseline
  exact (input.properSubgraphCT2Run ctx subgraph baseline).verified

/-- Exact terminal of every hypothetical proper-core CT2 execution. -/
theorem properSubgraphCT2Run_terminal (input : StaticInput)
    (ctx : Core.MinimalCounterexampleContext input.problem input.Target)
    (subgraph : PackedFiniteObject.ProperSubgraph ctx.G)
    (baseline : input.problem.Baseline subgraph.value) :
    (input.properSubgraphCT2Run ctx subgraph baseline).terminal =
      .deletionC2 := rfl

/-- Exact typed trace of every hypothetical proper-core CT2 execution. -/
theorem properSubgraphCT2Run_trace (input : StaticInput)
    (ctx : Core.MinimalCounterexampleContext input.problem input.Target)
    (subgraph : PackedFiniteObject.ProperSubgraph ctx.G)
    (baseline : input.problem.Baseline subgraph.value) :
    (input.properSubgraphCT2Run ctx subgraph baseline).trace =
      [.entry, .deletionDecision, .deletionC2Terminal] := rfl

/-- Totality of the proper-subgraph CT2 execution with its exact terminal and
typed trace. -/
theorem properSubgraphCT2Run_total (input : StaticInput)
    (ctx : Core.MinimalCounterexampleContext input.problem input.Target)
    (subgraph : PackedFiniteObject.ProperSubgraph ctx.G)
    (baseline : input.problem.Baseline subgraph.value) :
    ∃ run : CT2.CertifiedReductionRun ctx
        (input.properSubgraphCT2Input ctx subgraph baseline),
      run.terminal = .deletionC2 ∧
        run.trace = [.entry, .deletionDecision, .deletionC2Terminal] :=
  CT2.runCertifiedReduction_total ctx
    (input.properSubgraphCT2Input ctx subgraph baseline)

/-- The proper-core check is one local certified reduction. -/
theorem properSubgraphCT2Run_checks (input : StaticInput)
    (ctx : Core.MinimalCounterexampleContext input.problem input.Target)
    (subgraph : PackedFiniteObject.ProperSubgraph ctx.G)
    (baseline : input.problem.Baseline subgraph.value) :
    (input.properSubgraphCT2Run ctx subgraph baseline).checks = 1 := rfl

/-- Native degree-zero polynomial work bound for the proper-subgraph CT2
execution. -/
theorem properSubgraphCT2Run_polynomial (input : StaticInput)
    (ctx : Core.MinimalCounterexampleContext input.problem input.Target)
    (subgraph : PackedFiniteObject.ProperSubgraph ctx.G)
    (baseline : input.problem.Baseline subgraph.value) :
    (input.properSubgraphCT2Run ctx subgraph baseline).checks ≤
      (CT2.certifiedReductionBudget ctx).coefficient *
        ((CT2.certifiedReductionBudget ctx).size
            (input.properSubgraphCT2Input ctx subgraph baseline) + 1) ^
          (CT2.certifiedReductionBudget ctx).degree := by
  change 1 ≤ 1 * (1 + 1) ^ 0
  decide

/-- Framework-owned output combining the no-proper-core CT2 stage with the
already established edge-rooted CT1 and local dart-deletion CT2 stages on the
same selected graph. -/
structure EdgeRootedNoProperCorePrefix (input : StaticInput)
    (ctx : Core.MinimalCounterexampleContext input.problem input.Target) : Prop where
  fixedPrefix :
    (input.fixed ctx.G.Vertex).EdgeRootedDeletionPrefix
      (input.fixedContext ctx)
  noProperCore : ∀ subgraph : PackedFiniteObject.ProperSubgraph ctx.G,
    ¬ input.problem.Baseline subgraph.value
  properCoreTerminal : ∀
    (subgraph : PackedFiniteObject.ProperSubgraph ctx.G)
    (baseline : input.problem.Baseline subgraph.value),
    (input.properSubgraphCT2Run ctx subgraph baseline).terminal = .deletionC2
  properCoreTrace : ∀
    (subgraph : PackedFiniteObject.ProperSubgraph ctx.G)
    (baseline : input.problem.Baseline subgraph.value),
    (input.properSubgraphCT2Run ctx subgraph baseline).trace =
      [.entry, .deletionDecision, .deletionC2Terminal]
  properCoreTotal : ∀
    (subgraph : PackedFiniteObject.ProperSubgraph ctx.G)
    (baseline : input.problem.Baseline subgraph.value),
    ∃ run : CT2.CertifiedReductionRun ctx
        (input.properSubgraphCT2Input ctx subgraph baseline),
      run.terminal = .deletionC2 ∧
        run.trace = [.entry, .deletionDecision, .deletionC2Terminal]
  properCoreChecks : ∀
    (subgraph : PackedFiniteObject.ProperSubgraph ctx.G)
    (baseline : input.problem.Baseline subgraph.value),
    (input.properSubgraphCT2Run ctx subgraph baseline).checks = 1
  properCorePolynomial : ∀
    (subgraph : PackedFiniteObject.ProperSubgraph ctx.G)
    (baseline : input.problem.Baseline subgraph.value),
    (input.properSubgraphCT2Run ctx subgraph baseline).checks ≤
      (CT2.certifiedReductionBudget ctx).coefficient *
        ((CT2.certifiedReductionBudget ctx).size
            (input.properSubgraphCT2Input ctx subgraph baseline) + 1) ^
          (CT2.certifiedReductionBudget ctx).degree

/-- Construct the combined verified prefix on one packed minimal context. -/
def edgeRootedNoProperCorePrefix (input : StaticInput)
    (ctx : Core.MinimalCounterexampleContext input.problem input.Target) :
    EdgeRootedNoProperCorePrefix input ctx where
  fixedPrefix :=
    (input.fixed ctx.G.Vertex).edgeRootedDeletionPrefix
      (input.fixedContext ctx)
  noProperCore := input.noProperCore ctx
  properCoreTerminal := input.properSubgraphCT2Run_terminal ctx
  properCoreTrace := input.properSubgraphCT2Run_trace ctx
  properCoreTotal := input.properSubgraphCT2Run_total ctx
  properCoreChecks := input.properSubgraphCT2Run_checks ctx
  properCorePolynomial := input.properSubgraphCT2Run_polynomial ctx

/-- Select a lexicographically minimal counterexample by natural-number
well-ordering and execute the combined CT1/CT2 prefix.  This theorem performs
no finite-graph enumeration. -/
theorem exists_edgeRootedNoProperCorePrefix (input : StaticInput)
    {V : Type u} (object : FiniteObject V)
    (baseline : input.minimumDegree ≤ object.minDegree)
    (avoids : ¬ HasCycleWithLength object.graph input.LengthOK) :
    ∃ ctx : Core.MinimalCounterexampleContext
        (StaticInput.problem.{u} input) (StaticInput.Target.{u} input),
      (StaticInput.problem.{u} input).rank ctx.G ≤
          (StaticInput.problem.{u} input).rank
            (PackedFiniteObject.pack object) ∧
        EdgeRootedNoProperCorePrefix input ctx := by
  let initial : Core.AvoidingContext
      (StaticInput.problem.{u} input) (StaticInput.Target.{u} input) :=
    Core.AvoidingContext.ofBranch
      ⟨PackedFiniteObject.pack object, baseline, ()⟩ avoids
  obtain ⟨ctx, rankLe⟩ :=
    initial.exists_minimalCounterexample (fun _packed => ())
  exact ⟨ctx, rankLe, input.edgeRootedNoProperCorePrefix ctx⟩

/-- Native work certificate used by every proper-subgraph run in this graph
profile. -/
def properSubgraphBudget (input : StaticInput)
    (ctx : Core.MinimalCounterexampleContext input.problem input.Target) :
    Core.PolynomialCheckBudget (CT2.CertifiedReductionInput ctx) :=
  CT2.certifiedReductionBudget ctx

/-! ## Induced-path CT1 prefix -/

/-- Certificate-driven induced-path profile on the same packed ambient used
by the minimal-counterexample prefix. -/
def inducedPathProfile (input : StaticInput) (order : Nat) :
    InducedPath.Profile (P := input.problem) where
  Vertex := fun packed => packed.Vertex
  graph := fun packed => packed.object.graph
  order := order

/-- CT1 input obtained definitionally from the selected packed branch
context. -/
def inducedPathInput (input : StaticInput)
    (ctx : Core.MinimalCounterexampleContext input.problem input.Target) :
    CT1.Input input.problem where
  context := ctx.toBranchContext

/-- One explicit induced-path certificate on the selected packed graph. -/
abbrev InducedPathCertificate (input : StaticInput) (order : Nat)
    (ctx : Core.MinimalCounterexampleContext input.problem input.Target) :=
  (input.inducedPathProfile order).Code ctx.G

/-- Execute CT1 on one proof-carrying induced-path embedding. -/
def inducedPathRun (input : StaticInput) (order : Nat)
    (ctx : Core.MinimalCounterexampleContext input.problem input.Target)
    (certificate : input.InducedPathCertificate order ctx) :=
  (input.inducedPathProfile order).run
    (input.inducedPathInput ctx) certificate

/-- Complete certificate-driven CT1 output for the induced-path branch. -/
abbrev VerifiedInducedPathStage (input : StaticInput) (order : Nat)
    (ctx : Core.MinimalCounterexampleContext input.problem input.Target) :=
  (input.inducedPathProfile order).VerifiedStage
    (input.inducedPathInput ctx)

/-- Construct the complete CT1 output after the induced path has been forced
by graph mathematics external to the generic runner. -/
def verifiedInducedPathStage (input : StaticInput) (order : Nat)
    (ctx : Core.MinimalCounterexampleContext input.problem input.Target)
    (realization : HasInducedPath ctx.G.object.graph order) :
    input.VerifiedInducedPathStage order ctx :=
  (input.inducedPathProfile order).verifiedStage
    (input.inducedPathInput ctx) realization

/-! ## Induced-path packing CT12 prefix -/

/-- The exact successful CT1 outcome retained for framework routing. -/
noncomputable def inducedPathC1Source
    (input : StaticInput) (order : Nat)
    (ctx : Core.MinimalCounterexampleContext input.problem input.Target)
    (previous : input.VerifiedInducedPathStage order ctx) :
    Routes.CT1ToCT12.PackedC1
      (input.inducedPathProfile order).encoding.spec
      (input.inducedPathInput ctx) := by
  rcases previous.realization with ⟨certificate⟩
  exact ⟨(), certificate, trivial⟩

/-- Framework route adapter from the realized induced path to the selected
maximum-packing peel schedule.  Its evidence is the nonemptiness conclusion
needed by the graph proof, derived from the literal CT1 witness. -/
noncomputable def inducedPathPackingAdapter
    (input : StaticInput) (order : Nat) (positive : 0 < order)
    (ctx : Core.MinimalCounterexampleContext input.problem input.Target) :
    Routes.CT1ToCT12.SemanticAdapter
      (S := (input.inducedPathProfile order).encoding.spec)
      (input := input.inducedPathInput ctx)
      (CT12.ListPeeling.capability input.problem
        (InducedPathPacking.Window ctx.G.object order)) where
  trigger := fun _source => {
    load := (InducedPathPacking.profile ctx.G.object order positive).values.length
    state := CT12.ListPeeling.initialState
      (InducedPathPacking.profile ctx.G.object order positive).values
  }
  Evidence := fun _source _trigger =>
    InducedPathPacking.windows ctx.G.object order positive ≠ []
  evidence := by
    intro source
    rcases source with ⟨_unit, certificate, _accepts⟩
    exact InducedPathPacking.windows_nonempty_of_realization
      ctx.G.object order positive ⟨certificate⟩

/-- CT12 input produced only through the registered CT1→CT12 route. -/
noncomputable def inducedPathPackingRouteInput
    (input : StaticInput) (order : Nat) (positive : 0 < order)
    (ctx : Core.MinimalCounterexampleContext input.problem input.Target)
    (previous : input.VerifiedInducedPathStage order ctx) :=
  Routes.CT1ToCT12.buildInput
    (CT12.ListPeeling.capability input.problem
      (InducedPathPacking.Window ctx.G.object order))
    (input.inducedPathPackingAdapter order positive ctx)
    (input.inducedPathC1Source order ctx previous)

theorem inducedPathPackingRouteInput_eq
    (input : StaticInput) (order : Nat) (positive : 0 < order)
    (ctx : Core.MinimalCounterexampleContext input.problem input.Target)
    (previous : input.VerifiedInducedPathStage order ctx) :
    input.inducedPathPackingRouteInput order positive ctx previous =
      (InducedPathPacking.profile ctx.G.object order positive).input
        ctx.toBranchContext := by
  rfl

theorem inducedPathPackingRoute_id
    (input : StaticInput) (order : Nat) (positive : 0 < order)
    (ctx : Core.MinimalCounterexampleContext input.problem input.Target)
    (previous : input.VerifiedInducedPathStage order ctx) :
    ((Routes.CT1ToCT12.rule
      (CT12.ListPeeling.capability input.problem
        (InducedPathPacking.Window ctx.G.object order))
      (input.inducedPathPackingAdapter order positive ctx)).generate
        (input.inducedPathC1Source order ctx previous) ()).routeId =
      "CT1.terminal.c1->CT12" :=
  Routes.CT1ToCT12.generated_route_id _ _ _

/-- Framework-owned extension that consumes the exact induced-path CT1
output and retains a maximum/maximal vertex-disjoint packing, its CT12 audit,
and its induced-path-free remainder on the same selected graph. -/
structure InducedPathPackingPrefix (input : StaticInput)
    (order : Nat) (positive : 0 < order)
    (ctx : Core.MinimalCounterexampleContext input.problem input.Target) :
    Prop where
  previous : input.VerifiedInducedPathStage order ctx
  packingStage : InducedPathPacking.VerifiedStage ctx.G.object order positive
    ctx.toBranchContext
  routeId_eq :
    ((Routes.CT1ToCT12.rule
      (CT12.ListPeeling.capability input.problem
        (InducedPathPacking.Window ctx.G.object order))
      (input.inducedPathPackingAdapter order positive ctx)).generate
        (input.inducedPathC1Source order ctx previous) ()).routeId =
      "CT1.terminal.c1->CT12"
  routedInputExact :
    input.inducedPathPackingRouteInput order positive ctx previous =
      (InducedPathPacking.profile ctx.G.object order positive).input
        ctx.toBranchContext
  packingNonempty :
    InducedPathPacking.windows ctx.G.object order positive ≠ []

/-- Extend the exact prior prefix through the reusable induced-path packing
stage.  Nonemptiness is derived from the CT1 realization retained by the
predecessor; no packing conclusion is supplied by the caller. -/
noncomputable def inducedPathPackingPrefix
    (input : StaticInput) (order : Nat) (positive : 0 < order)
    (ctx : Core.MinimalCounterexampleContext input.problem input.Target)
    (previous : input.VerifiedInducedPathStage order ctx) :
    input.InducedPathPackingPrefix order positive ctx where
  previous := previous
  packingStage := InducedPathPacking.verifiedStage ctx.G.object order positive
    ctx.toBranchContext
  routeId_eq := input.inducedPathPackingRoute_id order positive ctx previous
  routedInputExact := input.inducedPathPackingRouteInput_eq order positive ctx
    previous
  packingNonempty := Routes.CT1ToCT12.evidence_preserved _
    (input.inducedPathPackingAdapter order positive ctx)
    (input.inducedPathC1Source order ctx previous)

/-! ## Induced-path attachment-classification CT10 prefix -/

/-- Exact attachment label computed with the selected packed object's
declared adjacency decision procedure. -/
def inducedPathAttachmentLabel (input : StaticInput) (order : Nat)
    (ctx : Core.MinimalCounterexampleContext input.problem input.Target)
    (path : SimpleGraph.pathGraph order ↪g ctx.G.object.graph)
    (outside : ctx.G.Vertex) : InducedPathAttachment.Label order := by
  letI : DecidableRel ctx.G.object.graph.Adj :=
    ctx.G.object.input.decideAdj
  exact InducedPathAttachment.attachmentLabel path outside

/-- Framework-owned extension retaining the complete CT12 packing output and
adding CT10's exhaustive finite table of legal path-attachment labels. -/
structure InducedPathPackingAttachmentPrefix
    (input : StaticInput) (order : Nat) (positive : 0 < order)
    (classification : InducedPathAttachment.Classification order
      input.LengthOK)
    (ctx : Core.MinimalCounterexampleContext input.problem input.Target) : Prop where
  previous : input.InducedPathPackingPrefix order positive ctx
  classificationStage :
    classification.profile.VerifiedStage ctx.toBranchContext
  actualLabelsLegal : ∀
    (path : SimpleGraph.pathGraph order ↪g ctx.G.object.graph)
    (outside : ctx.G.Vertex)
    (_outsidePath : ∀ position : Fin order, outside ≠ path position)
    (_attached : ∃ position, ctx.G.object.graph.Adj outside (path position)),
    InducedPathAttachment.Legal order input.LengthOK
      (input.inducedPathAttachmentLabel order ctx path outside)
  actualLabelsAccepted : ∀
    (path : SimpleGraph.pathGraph order ↪g ctx.G.object.graph)
    (outside : ctx.G.Vertex)
    (_outsidePath : ∀ position : Fin order, outside ≠ path position)
    (_attached : ∃ position, ctx.G.object.graph.Adj outside (path position)),
    classification.profile.Accepts
      (classification.decode.symm
        (input.inducedPathAttachmentLabel order ctx path outside))

/-- Extend the exact CT12 output through the reusable CT10 label
classification on the same branch context. -/
noncomputable def inducedPathPackingAttachmentPrefix
    (input : StaticInput) (order : Nat) (positive : 0 < order)
    (classification : InducedPathAttachment.Classification order
      input.LengthOK)
    (ctx : Core.MinimalCounterexampleContext input.problem input.Target)
    (previous : input.InducedPathPackingPrefix order positive ctx) :
    input.InducedPathPackingAttachmentPrefix order positive
      classification ctx where
  previous := previous
  classificationStage :=
    classification.profile.verifiedStage ctx.toBranchContext
  actualLabelsLegal := by
    intro path outside outsidePath attached
    letI : DecidableRel ctx.G.object.graph.Adj :=
      ctx.G.object.input.decideAdj
    exact InducedPathAttachment.attachmentLabel_legal_of_avoids
      input.LengthOK path outside outsidePath attached ctx.avoids
  actualLabelsAccepted := by
    intro path outside outsidePath attached
    apply (classification.accepts_iff_legal _).2
    rw [classification.decode.apply_symm_apply]
    letI : DecidableRel ctx.G.object.graph.Adj :=
      ctx.G.object.input.decideAdj
    exact InducedPathAttachment.attachmentLabel_legal_of_avoids
      input.LengthOK path outside outsidePath attached ctx.avoids

end StaticInput

end PackedMinimumDegreeCycle

end StructuralExhaustion.Graph
