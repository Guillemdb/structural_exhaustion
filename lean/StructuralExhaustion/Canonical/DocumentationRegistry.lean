import StructuralExhaustion.Core.Context
import StructuralExhaustion.Core.Enumeration
import StructuralExhaustion.Core.ExactHandoff
import StructuralExhaustion.Core.FiniteDisjointPacking
import StructuralExhaustion.Core.FiniteResidualLedger
import StructuralExhaustion.Core.FiniteSaturation
import StructuralExhaustion.Core.FiniteSearch
import StructuralExhaustion.Core.ResidualRefinement
import StructuralExhaustion.Core.WorkBudget
import StructuralExhaustion.Graph.EndpointParityCycle
import StructuralExhaustion.Graph.GreedyColoring
import StructuralExhaustion.Graph.InducedPath
import StructuralExhaustion.Graph.Mantel
import StructuralExhaustion.Graph.MaximumMatching
import StructuralExhaustion.Graph.PackedBoundariedGluing
import StructuralExhaustion.Graph.PackedMinimumDegreeCycle

namespace StructuralExhaustion.Canonical.Documentation

/-! Lean-owned navigation and explanatory metadata for the public framework
surface.  The referenced declarations are validated against the compiled
environment by `Canonical.Export`; example/workflow references are validated
when the web repository joins this catalog to the external example catalog. -/

inductive Layer where
  | core
  | graph
  deriving Repr, DecidableEq

namespace Layer

def key : Layer → String
  | .core => "core"
  | .graph => "graph"

end Layer

inductive Depth where
  | index
  | walkthrough
  deriving Repr, DecidableEq

namespace Depth

def key : Depth → String
  | .index => "index"
  | .walkthrough => "walkthrough"

end Depth

structure AudienceCopy where
  summary : String
  inputs : String
  result : String
  deriving Repr, DecidableEq

structure ExampleRef where
  exampleId : String
  workflowId : String
  title : String
  deriving Repr, DecidableEq

structure CapabilityDescriptor where
  capabilityId : String
  layer : Layer
  category : String
  title : String
  depth : Depth
  mathematician : AudienceCopy
  leanUser : AudienceCopy
  declarations : List Lean.Name
  relatedTacticIds : List String := []
  relatedCapabilityIds : List String := []
  examples : List ExampleRef := []
  deriving Repr, DecidableEq

structure TacticGuide where
  tacticId : String
  role : String
  useWhen : String
  leanEntry : String
  deriving Repr, DecidableEq

private def copy (summary inputs result : String) : AudienceCopy :=
  { summary := summary, inputs := inputs, result := result }

private def exampleRef (exampleId workflowId title : String) : ExampleRef :=
  { exampleId := exampleId, workflowId := workflowId, title := title }

def capabilities : List CapabilityDescriptor := [
  {
    capabilityId := "core.problem-context"
    layer := .core
    category := "Model the branch"
    title := "Problems and branch contexts"
    depth := .walkthrough
    mathematician := copy
      "Separate the ambient object, baseline hypothesis, rank, and accumulated branch state from any particular closure tactic."
      "An object class, a baseline property, a well-founded rank, and the facts currently retained on the branch."
      "A stable context that can be passed between tactics without silently changing the selected object or hypotheses."
    leanUser := copy
      "`Core.Problem` and its indexed contexts are the shared carrier for every CT input and typed transition."
      "Define the four problem fields once, then construct `BranchContext`, `AvoidingContext`, or `MinimalCounterexampleContext`."
      "Definitionally aligned contexts and projections used by CT capabilities and routes."
    declarations := [`StructuralExhaustion.Core.Problem,
      `StructuralExhaustion.Core.BranchContext,
      `StructuralExhaustion.Core.AvoidingContext,
      `StructuralExhaustion.Core.MinimalCounterexampleContext]
  },
  {
    capabilityId := "core.finite-enumeration"
    layer := .core
    category := "Make local work explicit"
    title := "Finite enumerations and observable order"
    depth := .walkthrough
    mathematician := copy
      "Turn the finite local universe used by a proof step into explicit data, distinguishing genuine sets from first-hit search orders."
      "A finite type or a duplicate-free local schedule."
      "An exhaustive finite carrier whose coverage and order are available to later proofs."
    leanUser := copy
      "Use `FinEnum` for total finite universes, `OrderedCollection` when first-hit order is observable, and `Finset` for unordered sums."
      "An explicit equivalence with `Fin n` or a duplicate-free list."
      "Reusable enumerations, membership theorems, and deterministic schedules."
    declarations := [`FinEnum,
      `StructuralExhaustion.Core.OrderedCollection,
      `StructuralExhaustion.Core.DependentEnumeration]
  },
  {
    capabilityId := "core.finite-search"
    layer := .core
    category := "Make local work explicit"
    title := "Certified finite search"
    depth := .index
    mathematician := copy
      "Search a declared finite family and retain either the first witness or a proof that no witness exists."
      "A finite schedule and a decidable local predicate."
      "A sound witness or an exhaustive negative certificate."
    leanUser := copy
      "`Core.FiniteSearch` packages deterministic first-hit computation with soundness and completeness theorems."
      "A `FinEnum` or list and a `DecidablePred`."
      "An evidence-carrying result with deterministic reference semantics."
    declarations := [`StructuralExhaustion.Core.FiniteSearch.search,
      `StructuralExhaustion.Core.FiniteSearch.search_sound,
      `StructuralExhaustion.Core.FiniteSearch.search_complete]
    relatedCapabilityIds := ["core.finite-enumeration"]
  },
  {
    capabilityId := "core.exact-handoff"
    layer := .core
    category := "Preserve provenance"
    title := "Exact predecessor handoff"
    depth := .walkthrough
    mathematician := copy
      "Advance a proof while recording that the next stage uses the exact predecessor already established, not a recomputed lookalike."
      "A verified predecessor and the next fact or dependent stage produced from it."
      "A successor carrying both new information and equality to the canonical predecessor."
    leanUser := copy
      "`ExactHandoff`, `ExactPropertyHandoff`, and `ExactStageHandoff` encode zero-copy predecessor provenance."
      "The expected value plus a property, producer, or dependent stage computed from the retrieved value."
      "Typed handoffs suitable for sequential proof nodes and generated workflow evidence."
    declarations := [`StructuralExhaustion.Core.ExactHandoff,
      `StructuralExhaustion.Core.ExactPropertyHandoff,
      `StructuralExhaustion.Core.ExactStageHandoff]
  },
  {
    capabilityId := "core.residual-refinement"
    layer := .core
    category := "Preserve provenance"
    title := "Residual refinement and occurrence ledgers"
    depth := .walkthrough
    mathematician := copy
      "Accumulate local decisions on one stable residual while retaining exactly which occurrence produced each fact."
      "A residual, an explicit schedule, and decidable refinements."
      "A sequential state with inherited facts, coverage, and uniquely indexed provenance."
    leanUser := copy
      "Use `ResidualRefinement.State.StageNode` for dependent proof prefixes and `FiniteResidualLedger.Ledger` for occurrence-sensitive schedules."
      "A stable residual carrier, fact predicates, stage producers, and a finite event schedule."
      "Composable nodes, indexed productions, and global coverage theorems."
    declarations := [`StructuralExhaustion.Core.ResidualRefinement.State,
      `StructuralExhaustion.Core.ResidualRefinement.State.StageNode,
      `StructuralExhaustion.Core.FiniteResidualLedger.Ledger]
    relatedCapabilityIds := ["core.exact-handoff", "core.finite-enumeration"]
  },
  {
    capabilityId := "core.finite-saturation"
    layer := .core
    category := "Close finite processes"
    title := "Well-founded saturation"
    depth := .index
    mathematician := copy
      "Repeatedly take the first enabled local move until no move remains, with termination visible in the proof."
      "Candidate moves, an enabledness test, a step operation, and a decreasing measure."
      "A saturated terminal state and a bounded list of chosen moves."
    leanUser := copy
      "`FiniteSaturation.Machine` owns first-enabled selection, well-founded execution, and terminal saturation."
      "A candidate enumeration, decision procedure, step, and strict decrease proof."
      "An execution, exact choice trace, saturation theorem, and iteration bound."
    declarations := [`StructuralExhaustion.Core.FiniteSaturation.Machine,
      `StructuralExhaustion.Core.FiniteSaturation.Machine.execute,
      `StructuralExhaustion.Core.FiniteSaturation.Machine.Execution.terminal_saturated]
    relatedCapabilityIds := ["core.finite-search", "core.work-budget"]
  },
  {
    capabilityId := "core.disjoint-packing"
    layer := .core
    category := "Close finite processes"
    title := "Maximum finite disjoint packing"
    depth := .walkthrough
    mathematician := copy
      "Select a maximum family of pairwise disjoint nonempty supports and turn maximality into a saturation statement."
      "Finite items, their nonempty finite supports, and a finite host."
      "A maximum packing that intersects every omitted item and is bounded by the host size."
    leanUser := copy
      "`FiniteDisjointPacking.Profile` proof-selects a maximum packing without exposing an executable powerset search."
      "Finite vertex and item types plus a nonempty support map."
      "The selected values, maximum/saturation proofs, and symbolic cardinality bounds."
    declarations := [`StructuralExhaustion.Core.FiniteDisjointPacking.Profile,
      `StructuralExhaustion.Core.FiniteDisjointPacking.Profile.maximum_saturated]
    relatedCapabilityIds := ["core.finite-enumeration"]
    relatedTacticIds := ["CT12"]
    examples := [exampleRef "even-cycle" "main" "Minimum degree three gives an even cycle"]
  },
  {
    capabilityId := "core.work-budget"
    layer := .core
    category := "Certify execution"
    title := "Counted work and polynomial budgets"
    depth := .walkthrough
    mathematician := copy
      "Make the number of primitive local checks part of the theorem rather than an informal complexity claim."
      "An input-size measure and an exact or compositional check count."
      "A certified polynomial envelope that composes across sequential and branching computations."
    leanUser := copy
      "`Counted` tracks exact checks; `PolynomialCheckBudget` supplies constant, zero, sum, scale, branch, and pullback combinators."
      "A counted computation and proofs bounding its checks by a declared size polynomial."
      "Reusable complexity certificates without re-proving arithmetic for framework composition."
    declarations := [`StructuralExhaustion.Core.Counted,
      `StructuralExhaustion.Core.PolynomialCheckBudget,
      `StructuralExhaustion.Core.PolynomialCheckBudget.add,
      `StructuralExhaustion.Core.PolynomialCheckBudget.branch]
  },
  {
    capabilityId := "graph.finite-object"
    layer := .graph
    category := "Represent graphs"
    title := "Finite Mathlib graph input"
    depth := .walkthrough
    mathematician := copy
      "Use an ordinary finite simple graph while making the vertex order and adjacency decisions needed by deterministic proof machines explicit."
      "A Mathlib simple graph with a finite vertex enumeration."
      "Graph invariants, ordered neighborhoods, darts, degrees, and a shared structural-exhaustion problem context."
    leanUser := copy
      "`Graph.FiniteObject` bundles a `SimpleGraph` with `FiniteInput`; it does not introduce a second graph representation."
      "A Mathlib graph, explicit `FinEnum` vertices, and decidable adjacency."
      "Canonical graph problem/context values and reusable finite graph operations."
    declarations := [`StructuralExhaustion.Graph.FiniteObject,
      `StructuralExhaustion.Graph.FiniteObject.problem,
      `StructuralExhaustion.Graph.FiniteObject.context]
    relatedCapabilityIds := ["core.problem-context", "core.finite-enumeration"]
  },
  {
    capabilityId := "graph.induced-path"
    layer := .graph
    category := "Certificates and local structure"
    title := "Proof-carrying induced paths"
    depth := .walkthrough
    mathematician := copy
      "Treat an induced path embedding itself as the finite certificate, avoiding enumeration of vertex tuples or subgraphs."
      "A literal Mathlib induced graph embedding of a path."
      "Target realization or an exact induced-path-free residual."
    leanUser := copy
      "`Graph.InducedPath.Profile` supplies CT1 encoding, exact executions, reflection, traces, totality, and constant certificate work."
      "A target predicate, path order, and proof-carrying embedding."
      "A reusable CT1 profile with certificate-driven positive and avoiding runs."
    declarations := [`StructuralExhaustion.Graph.InducedPath.Profile,
      `StructuralExhaustion.Graph.InducedPath.Profile.encoding,
      `StructuralExhaustion.Graph.InducedPath.Profile.run]
    relatedCapabilityIds := ["graph.finite-object"]
    relatedTacticIds := ["CT1"]
    examples := [exampleRef "even-cycle" "main" "Minimum degree three gives an even cycle"]
  },
  {
    capabilityId := "graph.endpoint-parity-cycle"
    layer := .graph
    category := "Paths and cycles"
    title := "Endpoint-parity cycle pipeline"
    depth := .walkthrough
    mathematician := copy
      "Close a maximal path, overload two parity classes at an endpoint, and convert equal-parity neighbors into an even cycle."
      "A finite graph of minimum degree at least three and an endpoint-maximal path."
      "An explicit even-cycle certificate."
    leanUser := copy
      "`EndpointParityCycle.Profile` composes maximal-path selection, CT6, the registered CT6-to-CT9 route, CT9, chord construction, and CT1 validation."
      "A `FiniteObject` and the reusable minimum-degree/even-cycle profile."
      "Aligned runs, typed traces, a cycle certificate, and final CT1 validation."
    declarations := [`StructuralExhaustion.Graph.EndpointParityCycle.Profile,
      `StructuralExhaustion.Graph.EndpointParityCycle.Profile.ct6Run,
      `StructuralExhaustion.Graph.EndpointParityCycle.Profile.evenCycle]
    relatedCapabilityIds := ["graph.finite-object"]
    relatedTacticIds := ["CT6", "CT9", "CT1"]
    examples := [exampleRef "even-cycle" "main" "Minimum degree three forces an even cycle"]
  },
  {
    capabilityId := "graph.packed-reduction"
    layer := .graph
    category := "Reduction and replacement"
    title := "Ranked proper-subgraph reduction"
    depth := .walkthrough
    mathematician := copy
      "Choose a smaller finite graph by lexicographic vertex/edge rank and transport cycle information through an injective graph map."
      "A selected packed proper subgraph and preservation proofs."
      "A certified minimality contradiction or deletion-critical residual."
    leanUser := copy
      "`PackedMinimumDegreeCycle` owns varying vertex types, lexicographic rank, cycle transport, and certificate-driven CT2 execution."
      "One proof-specified proper subgraph; no universe of graphs or subgraphs."
      "Constant-work CT2 reduction, exact trace, and non-properness consequences."
    declarations := [`StructuralExhaustion.Graph.PackedFiniteObject,
      `StructuralExhaustion.Graph.PackedFiniteObject.ProperSubgraph]
    relatedCapabilityIds := ["graph.finite-object", "core.work-budget"]
    relatedTacticIds := ["CT2"]
    examples := [exampleRef "even-cycle" "main" "Minimum degree three gives an even cycle"]
  },
  {
    capabilityId := "graph.boundaried-gluing"
    layer := .graph
    category := "Reduction and replacement"
    title := "Literal boundaried replacement"
    depth := .walkthrough
    mathematician := copy
      "Replace a graph piece only after proving that it has the same response in every compatible outside context."
      "Finite boundary labels, a piece, a smaller replacement, and a compatible outside graph."
      "Literal glued-graph transport and a certified uncompressibility conclusion."
    leanUser := copy
      "`PackedBoundariedGluing` derives whole-object decrease, baseline preservation, and target transport before invoking certified CT3 compression."
      "Packed boundaried pieces, boundary-degree data, gluing semantics, and one replacement certificate."
      "A one-check CT3 stage with exact response and minimality consequences."
    declarations := [`StructuralExhaustion.Graph.PackedBoundariedGluing.BoundariedGraph,
      `StructuralExhaustion.Graph.PackedBoundariedGluing.Context,
      `StructuralExhaustion.Graph.PackedBoundariedGluing.glueGraph]
    relatedCapabilityIds := ["graph.packed-reduction", "core.exact-handoff"]
    relatedTacticIds := ["CT3"]
    examples := [exampleRef "even-cycle" "main" "Minimum degree three gives an even cycle"]
  },
  {
    capabilityId := "graph.maximum-matching"
    layer := .graph
    category := "Packing and construction"
    title := "Maximum matching from induced-edge packing"
    depth := .walkthrough
    mathematician := copy
      "Specialize maximum disjoint support packing to edges; maximal saturation makes the unmatched remainder edgeless."
      "A finite simple graph."
      "A maximum matching, a vertex partition, and an edgeless unmatched remainder."
    leanUser := copy
      "`Graph.MaximumMatching` specializes induced-path packing at order two and audits the selected edge list with CT12."
      "A `FiniteObject`; the framework supplies edge supports and the selected maximum family."
      "Maximum and partition theorems, exact CT12 exhaustion, and linear trace bounds."
    declarations := [`StructuralExhaustion.Graph.MaximumMatching.maximum,
      `StructuralExhaustion.Graph.MaximumMatching.partition,
      `StructuralExhaustion.Graph.MaximumMatching.remainder_no_edges]
    relatedCapabilityIds := ["core.disjoint-packing", "graph.induced-path"]
    relatedTacticIds := ["CT12"]
    examples := [exampleRef "even-cycle" "main" "Minimum degree three gives an even cycle"]
  },
  {
    capabilityId := "graph.greedy-coloring"
    layer := .graph
    category := "Packing and construction"
    title := "Verified greedy coloring"
    depth := .walkthrough
    mathematician := copy
      "Peel vertices in a fixed order, choose a color missing from later neighbors, and assemble the choices into a proper coloring."
      "A finite graph and a color bound larger than every later-neighbor set."
      "A proper coloring, with the maximum-degree-plus-one theorem as the canonical instance."
    leanUser := copy
      "`Graph.GreedyColoring` combines a CT12 list audit, repeated CT4 functional-cardinality runs, and CT1 certificate validation."
      "Only a `FiniteObject`; the graph layer generates the schedule, step profiles, fold, and target encoding."
      "A Mathlib `Colorable` proof plus exact CT12, CT4, and CT1 executions."
    declarations := [`StructuralExhaustion.Graph.GreedyColoring.colorOrder,
      `StructuralExhaustion.Graph.GreedyColoring.peelingRun,
      `StructuralExhaustion.Graph.GreedyColoring.colorable_maxDegree_succ]
    relatedCapabilityIds := ["graph.finite-object", "core.finite-saturation"]
    relatedTacticIds := ["CT12", "CT4", "CT1"]
    examples := [exampleRef "greedy-coloring" "coloring" "Deterministic greedy coloring"]
  },
  {
    capabilityId := "graph.mantel"
    layer := .graph
    category := "Extremal counting"
    title := "Mantel localization"
    depth := .walkthrough
    mathematician := copy
      "Turn failure of a global edge bound into a negative sum, localize it to one oriented edge, and contradict triangle-free neighborhood disjointness."
      "A finite triangle-free graph and a hypothetical violation of the quarter-square edge bound."
      "Mantel's theorem, together with the exact offending-edge residual used in the contradiction."
    leanUser := copy
      "`Graph.Mantel` owns the degree identities and Cauchy-Schwarz estimate, then invokes CT11's negative-budget profile."
      "A `FiniteObject` and `CliqueFree 3`; the application supplies no CT11 capability."
      "The CT11 run, localized residual, contradiction theorem, and final Mathlib-native edge bound."
    declarations := [`StructuralExhaustion.Graph.Mantel.profile,
      `StructuralExhaustion.Graph.Mantel.run,
      `StructuralExhaustion.Graph.Mantel.edgeCount_le_card_sq_div_four_of_triangleFree]
    relatedCapabilityIds := ["graph.finite-object", "core.work-budget"]
    relatedTacticIds := ["CT11"]
    examples := [exampleRef "mantel" "proof" "Mantel bound by CT11 localization"]
  }
]

def tacticGuides : List TacticGuide := [
  { tacticId := "CT1", role := "Realization", useWhen := "A target has a finite witness or certificate search.", leanEntry := "Define a target encoding or certificate encoding, then run the generated CT1 capability." },
  { tacticId := "CT2", role := "Reduction", useWhen := "Minimality should rule out a deletion or an exhaustive local replacement.", leanEntry := "Choose deletion-only, local-deletion, or certified-reduction profiles before defining a raw capability." },
  { tacticId := "CT3", role := "Compression", useWhen := "Two local pieces can be compared through exact finite response coordinates.", leanEntry := "Supply a target-compression contract or literal packed replacement certificate." },
  { tacticId := "CT4", role := "Charging", useWhen := "Demands must be assigned to eligible payers under a capacity bound.", leanEntry := "Use the functional-cardinality profile when eligibility is functional." },
  { tacticId := "CT5", role := "Aggregation", useWhen := "Local witnesses either fail support or contribute to a global ledger.", leanEntry := "Provide finite sites, dependent witnesses, support decisions, and contributions." },
  { tacticId := "CT6", role := "Ordered failure", useWhen := "The first failed local condition matters, or every condition being active yields a ledger.", leanEntry := "Provide the observable failure order and a decidable failure predicate." },
  { tacticId := "CT7", role := "Context classification", useWhen := "Two objects must be separated by a finite context or certified response-neutral.", leanEntry := "Provide exact realization and response functions over finite contexts." },
  { tacticId := "CT8", role := "Repetition", useWhen := "Repeated exact types in a finite state sequence permit comparison or removal.", leanEntry := "Enumerate exact types and response contexts and supply the removal operation." },
  { tacticId := "CT9", role := "Overload", useWhen := "A finite label partition must contain a fibre beyond its capacity.", leanEntry := "Supply items, labels, the label map, and capacity; use parity capacity-one when applicable." },
  { tacticId := "CT10", role := "Classification", useWhen := "A finite refinement table yields a direct case, a missing class, or promotion.", leanEntry := "Use exhaustive classification for a decidable accepted-candidate table." },
  { tacticId := "CT11", role := "Localization", useWhen := "A negative finite total must have a locally negative cell.", leanEntry := "Use `NegativeBudgetProfile` for universally admissible cells." },
  { tacticId := "CT12", role := "Peeling", useWhen := "A structurally decreasing process peels objects until exhaustion or saturation.", leanEntry := "Prefer list peeling or disjoint packing for the standard schedule shapes." },
  { tacticId := "CT13", role := "Tiered charging", useWhen := "A first payer tier may fail and requires canonical fallback and reconciliation.", leanEntry := "Provide both payer tiers, fallback costs, and the deficit comparison." },
  { tacticId := "CT14", role := "Aggregate capacity", useWhen := "Member lower masses must be compared with optional capacities and multiplicities.", leanEntry := "Enumerate members and labels and supply lower mass and capacity data." },
  { tacticId := "CT15", role := "Rank forcing", useWhen := "Target-relative coordinates either exhibit a rank drop or fill a capacity ledger.", leanEntry := "Provide finite coordinates, target dependence, charge, and capacity." },
  { tacticId := "CT16", role := "Closed type", useWhen := "Whole-support exhaustion produces a closed code to compare with a target code.", leanEntry := "Supply support decisions, code computation, and target-code equality." },
  { tacticId := "CT17", role := "Target thickening", useWhen := "Bounded offsets, scales, survivors, and orbit arithmetic can be exhausted locally.", leanEntry := "Provide the finite compatibility and scale universes with arithmetic deciders." }
]

end StructuralExhaustion.Canonical.Documentation
