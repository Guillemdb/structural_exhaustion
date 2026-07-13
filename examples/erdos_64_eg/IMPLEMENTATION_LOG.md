# Erdős Problem 64 implementation state

This ledger records the Lean-checked proof content in
`examples/erdos_64_eg` as of 2026-07-13.

The theorem-bearing endpoint is
`Erdos64EG.Internal.exists_verifiedP13LabelAlgebraPrefix`:

```lean
(object : Object V) → Baseline object → ¬ Target object →
  ∃ ctx : Core.MinimalCounterexampleContext
      packedStaticInput.problem packedStaticInput.Target,
    packedStaticInput.problem.rank ctx.G ≤
        packedStaticInput.problem.rank
          (Graph.PackedFiniteObject.pack object) ∧
      VerifiedP13LabelAlgebraPrefix ctx
```

Natural-number well-ordering selects a counterexample minimal in the
manuscript order `(number of vertices, number of edges)`. The verified output
contains:

- the exact edge-rooted Mersenne CT1 avoiding execution;
- the no-proper-core certificate-driven CT2 stage;
- the registered CT1-to-local-deletion CT2 result;
- deletion criticality and independence of the vertices of degree at least
  four; and
- the CT3 boundaried-replacement stage: boundary-degree fibres, universal
  context response, the replacement contradiction, and hereditary
  target-uncompressibility; and
- the CT1 induced-`P₁₃` stage: the exact avoiding execution, HSS closure,
  forced induced embedding, C1 execution, totality, and constant work bound;
  and
- the CT12 induced-`P₁₃` packing stage: maximum cardinality, maximal
  saturation, an exhausted selected-list execution, the exact
  `|R| + 13 p₁₃ = |V(G)|` partition, hereditary `P₁₃`-freeness of the
  remainder, and absence of every finite internal subgraph of minimum degree
  at least three; and
- the CT10 induced-`P₁₃` attachment-label stage: compact exact coding of
  all `8192` subsets, symbolic equivalence between the code test and the
  manuscript gap test, the complete `399`-row table with size distribution
  `13,60,122,122,63,17,2`, the exact `C_s` and `Ω₂` relations, and proof
  that every actual nonempty attachment in the selected graph belongs to the
  accepted table.

The endpoint accepts only the internal graph, its minimum-degree-three proof,
and target avoidance. It accepts no CT outcome, reduction conclusion,
minimality theorem, route result, or author-supplied closure contract.
The Hegde--Sandeep--Shashank theorem used at node `[16]` is the repository's
sole explicitly trusted external theorem declaration.

## Official boundary

`Erdos64EG.OfficialStatement` is the pinned Mathlib `SimpleGraph`
formulation: every finite graph of minimum degree at least three contains a
simple cycle of length `2 ^ k` for some `k ≥ 2`.

The internal executable boundary is established by:

- `PowerOfTwoLength`, whose exponent is searched in `Fin (length + 1)`;
- `powerOfTwoLength_iff`, proving equivalence with the unbounded exponent
  statement;
- `staticInput`, instantiating `Graph.MinimumDegreeCycle.StaticInput` at
  minimum degree three; and
- `target_iff_official_conclusion`, identifying the internal target with the
  official conclusion on the same Mathlib graph.

`Graph.FiniteObject` adds an explicit `FinEnum` vertex schedule and adjacency
decision procedure to the Mathlib graph. These data determine local machine
order and do not define a separate graph representation.

## Current proof-flow execution map

| Manuscript section and nodes | Prior verified input | CT/profile | Verified output | Work bound |
|---|---|---|---|---|
| `def:mersenne-return-set`, `lem:return-equivalence`, nodes `[5]`–`[7]` | Official internal graph and baseline | CT1 target-certificate profile | Exact cycle/return equivalence, C1 execution from a supplied return, and typed avoiding execution with universal Mersenne-disjoint return sets | One check on C1; zero checks on the avoiding execution |
| `lem:no-proper-core`, node `[8]` | Target-avoiding lexicographically minimal packed context and one explicit proper-subgraph certificate | CT2 certified-reduction profile through `Graph.PackedMinimumDegreeCycle` | Every proper subgraph has minimum degree at most two; exact deletion-C2 terminal and trace; totality and semantic contradiction | One local certificate check; degree-zero polynomial budget |
| `lem:deletion-critical`, nodes `[9]`, `[10]`, `[67]` | The fixed-vertex view of the same packed minimal context and its exact CT1 avoiding output | Registered CT1-to-local-deletion CT2 route | Exact disabled dart discovery, a degree-three endpoint on every edge, and independence of degree-at-least-four vertices | At most one scan of the declared dart list; each explicit deletion-C2 branch has one local check |
| `def:boundaried-gluing` through `cor:uncompressible`, nodes `[11]`–`[14]` (also reused at `[36]`–`[39]`) | `VerifiedNoProperCorePrefix` on the same packed minimal context | Literal `Graph.PackedBoundariedGluing` semantics plus the CT3 certified-reduction kernel | Exact vertex and edge arithmetic for gluing; local-to-global lexicographic decrease; degree preservation at atom, context, and boundary vertices; target and baseline transport through a reconstruction isomorphism; replacement contradiction and hereditary target-uncompressibility for normalized decompositions with nonempty boundary; composed `VerifiedBoundariedReplacementPrefix` | Proof-level construction only: one certified reduction, no enumeration of contexts, graphs, subgraphs, or replacements |
| `thm:p13free`, `cor:p13-exists`, nodes `[15]`–`[16]` | `VerifiedBoundariedReplacementPrefix` and target avoidance on the identical packed minimal context | CT1 target-certificate profile through `Graph.InducedPath.Profile`; HSS is the sole trusted external closure | Literal `P₁₃`-free avoiding terminal and trace; HSS contradiction; induced `P₁₃` realization; exact C1 terminal and trace; totality; composed `VerifiedInducedP13Prefix` retaining all preceding outputs | Zero checks on the proof-carrying avoiding run; one check on a supplied Mathlib induced embedding; degree-zero polynomial budgets; no tuple, path, subgraph, or graph universe is enumerated |
| `sec:remainder`, node `[17]` and the packing-derived clauses of `[25]`–`[27]` | `VerifiedInducedP13Prefix` on the identical selected packed graph | CT12 disjoint-packing profile through `Graph.InducedPathPacking` | A maximum vertex-disjoint induced-`P₁₃` family; maximal saturation; exact exhausted CT12 run with `p₁₃` iterations; `13 p₁₃ ≤ n`; `|R| + 13 p₁₃ = n`; `R` and every induced subgraph of `R` are `P₁₃`-free; HSS rules out every finite internal subgraph of minimum degree at least three; composed `VerifiedP13PackingPrefix` retaining every prior stage | CT12 visits exactly the selected packing list, once per packed window and hence at most `n` iterations; trace length at most `4n + 3`; the embedding and packing universes are not materialized |
| `lem:labels` and the definitions of `C_s` and `Ω₂`, node `[18]` | `VerifiedP13PackingPrefix` on the identical selected packed graph | CT10 exact accepted-class profile through `CT10.ExhaustiveClassification` and `Graph.InducedPathAttachment` | Exact legality equivalence; `8192` compact candidates; `399` legal labels; size distribution `13,60,122,122,63,17,2`; legal sizes `1`–`7`; exhaustive terminal, exact typed trace, semantic validity and totality; exact `C_s` and `Ω₂`; every actual attachment accepted; composed `VerifiedP13LabelAlgebraPrefix` retaining the exact CT12 predecessor | `167792 = 8192 + 399 + 399²` primitive candidate/direct/row checks, bounded quadratically in the explicit candidate universe; no graph, path, subgraph, or context universe is enumerated |

The next dependency-ready manuscript frontier is the non-near-cubic surplus
branch at nodes `[19]`–`[20]`, including its expanded nodes `[125]`–`[144]`.
Node `[21]` is reached only after the no-surplus branch of that routing. The
density-dependent assertion that `R` is large at nodes `[25]`–`[26]` remains
downstream and is not claimed by the packing or label-algebra stages.

## Nodes `[5]`–`[7]`: edge-rooted Mersenne CT1

### Reusable graph layer

`StructuralExhaustion.Graph.EdgeRootedReturn` packages:

- an oriented Mathlib dart `e = uv`;
- a walk from `v` to `u` in the graph with `e` deleted;
- a simple-path proof; and
- the selected predicate on the return length.

The graph layer proves:

- `EdgeRootedReturn.ofCycle`;
- `EdgeRootedReturn.cycle` and `cycle_isCycle`;
- `hasCycleWithLength_iff_hasEdgeRootedReturn`;
- `hasEdgeRootedReturn_iff_exists_mem_returnSet`; and
- `noCycleWithLength_iff_returnSets_disjoint`.

`Graph.MinimumDegreeCycleRouted` supplies the target certificate encoding,
positive and avoiding CT1 runners, exact return-set consequence, registered
local-deletion route, and fixed-vertex prefix.

### Erdős arithmetic and execution

`Erdos64EG.Internal.TargetAlgebra` defines:

- `MersenneLength r := PowerOfTwoLength (r + 1)`;
- `MersenneSet` and the manuscript return set;
- `mersenneLength_iff`;
- `hasPowerCycle_iff_hasRootedReturn`;
- `target_iff_hasMersenneReturn`; and
- `not_target_iff_returnSets_disjoint`.

`runMersenneCT1` and `runCT1` reach `c1Terminal` with trace

```text
entry → equivalenceCertification → realizationDecision → c1Terminal
```

and check count one. `runAvoidingCT1` reaches `avoidingTerminal` with the same
prefix and check count zero. `runAvoidingCT1_returnSets_disjoint` extracts the
universal Mersenne-disjointness theorem from that execution.

The `K₄` fixture constructs the four-cycle, its length-three rooted return,
and the exact C1 terminal, trace, and check count.

## Node `[8]`: no proper core

### Packed finite graphs and manuscript rank

`StructuralExhaustion.Graph.PackedFiniteObject` hides the finite graph's
vertex type inside the ambient object. Its rank is

```text
vertexCount ^ 3 + edgeCount.
```

The graph layer proves that a simple graph has at most `vertexCount ^ 2`
edges. Consequently:

- fewer vertices always give a smaller rank; and
- at equal vertex count, fewer edges give a smaller rank.

Thus `Core.AvoidingContext.exists_minimalCounterexample` selects the
manuscript's lexicographic minimum by proof-level `Nat.find`. It does not
enumerate finite graphs.

`PackedFiniteObject.ProperSubgraph G` contains exactly the local mathematical
data needed for a proper subgraph:

- a finite graph `H`;
- an embedding of `V(H)` into `V(G)`;
- inclusion of the mapped edge relation in `G`; and
- strict lexicographic decrease, either in vertex count or, at equal vertex
  count, in edge count.

`CycleWithLength.mapHom` and
`ProperSubgraph.hasCycleWithLength_mono` transport an accepted simple cycle in
`H` through the injective Mathlib graph homomorphism, preserving its exact
walk length.

### CT2 execution

`CT2.CertifiedReductionInput` receives the proof-carrying smaller object, its
baseline, and target transport. `CT2.runCertifiedReduction` constructs the
canonical deletion-C2 execution:

```text
entry → deletionDecision → deletionC2Terminal
```

The framework proves its typed path, semantic contradiction, totality, check
count one, and constant degree-zero polynomial budget.

`Graph.PackedMinimumDegreeCycle.StaticInput.properSubgraphCT2Run` instantiates
this profile for any minimum-degree/cycle target. Its semantic theorem is
`noProperCore`. The Erdős theorem
`properSubgraph_minDegree_le_two` specializes the conclusion to

```lean
∀ H : Graph.PackedFiniteObject.ProperSubgraph ctx.G,
  H.value.object.minDegree ≤ 2
```

`EdgeRootedNoProperCorePrefix` bundles this result with the edge-rooted CT1
and local dart-deletion CT2 prefix on `fixedContext ctx`.
`noProperCorePrefix_previous` states this provenance at the concrete Erdős
boundary.

## Nodes `[9]` and `[10]`: deletion criticality

The registered route identifier is

```text
CT1.residual.avoiding->CT2.localDeletion
```

It consumes the actual CT1 avoiding residual, transports the selected
minimality kernel through the target bridge, and performs finite local dart
discovery. The graph profile supplies dart deletion, exact edge-count
decrease, endpoint-slack baseline preservation, and cycle transport through
graph inclusion.

The concrete results are:

- `localRoute_disabled`;
- `deletionCriticality`, proving that every edge has a degree-three endpoint;
- `highDegree_independent`; and
- `VerifiedCT1CT2Prefix`, recording CT1 terminal/trace, route provenance,
  disabled discovery, return-set disjointness, and both graph consequences.

The dart schedule is derived from the declared vertex enumeration and has at
most the ordered-pair schedule size. No subgraph or ambient graph universe is
materialized.

## Nodes `[11]`–`[14]`: one boundaried-replacement CT3 stage

Chapter 1 draws four consecutive nodes, but they are one CT3 execution block:

```text
[11] boundaried atom and boundary-degree fibre
  → [12] universal outside-context response
  → [13] certified replacement compression terminal
  → [14] hereditary target-uncompressibility
```

The same CT3 semantics are invoked again by the rank-drop decisions at nodes
`[36]`–`[39]`; those later consumers are not independently implemented here.

### Reusable airtight CT3 semantics and runner

`Graph.PackedBoundariedGluing` is the sole boundaried replacement interface.
A piece is a
finite graph on `T ⊕ Internal`; an outside context is normalized to contain no
boundary--boundary edge, so those edges are owned by the piece. Every ordinary
decomposition admits this ownership convention, and replacements remain free
to change boundary--boundary edges.

The literal union gluing proves:

- the exact glued vertex count;
- disjointness of the two mapped edge sets and exact edge-count additivity;
- strict whole-graph lexicographic rank decrease from only a strict local
  piece decrease;
- exact degree formulas for replacement-internal, outside-internal, and
  boundary vertices;
- preservation of minimum degree from equal local boundary degrees and the
  replacement's internal degree bound; and
- invariance of rank, minimum degree, and the cycle-length target under the
  graph isomorphism reconstructing the selected ambient graph.

`MinimumDegreeCycleReplacement.Compression` therefore contains no asserted
whole-glue rank or baseline fact. Its mathematical fields are boundary-degree
equality, one-way obstruction inclusion, internal target-freeness, the internal
degree bound, and local lexicographic smallness. A target-complete quotient
constructs this one-way relation as a special case. `certifiedInput` derives every global obligation
before invoking the shared minimality kernel.

`CT3.CertifiedCompression` owns only the canonical typed path

```text
entry → vectorComputation → compressionSearch → compressionTerminal
```

and the reduction-kernel contradiction after the graph layer has constructed
the genuine `Core.SmallerObject`. `runCertifiedCompression_total` proves
totality and `certifiedCompressionBudget` records one degree-zero check.

The current theorem explicitly requires `Nonempty T`. This is the structural
boundary fact for a proper connected atom in a connected ambient graph. The
Lean CT3 stage does not yet derive ambient connectedness and hence does not
claim the empty-boundary whole-graph case; closed representatives belong to
the manuscript's separate closed-profile branch.

### Erdős declarations and provenance

`ConcreteCT3` is a narrow instantiation at minimum degree three and the
power-of-two-cycle target. It exports only aliases for the framework-owned
`Piece`, `Context`, `ProperAtom`, `Compression`, and `VerifiedStage` types.
Boundary-fibre separation, context universality, composition, target defects,
the compression terminal and trace, totality, work bounds, and impossibility
are consumed directly from
`Graph.PackedBoundariedGluing.MinimumDegreeCycleReplacement`; the Erdős
package does not restate those theorems under application-local names.

`verifiedBoundariedReplacementPrefix` takes the exact
`VerifiedNoProperCorePrefix` as its input. The provenance theorem
`boundariedReplacementPrefix_previous` recovers that preceding output, while
`boundariedReplacementPrefix_uncompressible` extracts the literal-gluing
node `[14]` conclusion from the composed stage. The public endpoint
`exists_verifiedBoundariedReplacementPrefix` accepts only the official
internal object, its baseline, and target avoidance.

## Nodes `[15]`–`[16]`: one induced-`P₁₃` CT1 stage

The diagram's branch test and HSS leaf are one CT1 execution block:

```text
[15] decide whether an induced P₁₃ realization exists
  ├─ avoiding → literal P₁₃-freeness
  │               → [16] HSS target cycle → contradict target avoidance
  └─ realization → proof-carrying induced P₁₃ embedding → C1 terminal
```

Node `[16]` is therefore not a separate CT. It closes the avoiding residual
of the CT1 realization decision at node `[15]`.

### Reusable induced-path profile

`StructuralExhaustion.Graph.HasInducedPath G k` is Mathlib's literal induced
containment relation

```lean
SimpleGraph.IsIndContained (SimpleGraph.pathGraph k) G.
```

Its certificate is a graph embedding `pathGraph k ↪g G`. The embedding's
injectivity supplies the distinct vertices, and adjacency reflection supplies
both the path edges and the absence of chords.

`Graph.InducedPath.Profile` generates:

- `TargetCertificateEncoding` with the embedding as its code;
- `Profile.run` and `Profile.runAvoiding`;
- positive and avoiding terminal, trace, semantic, and totality theorems;
- one-check and zero-check degree-zero polynomial budgets; and
- `VerifiedStage`, which retains an actual existential C1 execution.

`Graph.PackedMinimumDegreeCycle.inducedPathProfile` instantiates that API on
the varying-vertex packed ambient. `inducedPathInput` is definitionally the
selected minimal context's inherited branch; it does not construct a fresh
context. `EdgeRootedBoundariedInducedPathPrefix` retains the exact CT3 prefix
as `previous` and adds the induced-path stage on the same graph.
This is ordinary typed theorem composition, not a residual-to-trigger flow,
so no registered route is introduced.

### Sole external theorem

`StructuralExhaustion.Graph.External.HegdeSandeepShashank.
p13Free_hasPowerOfTwoCycle` records exactly the cited theorem: a finite
induced-`P₁₃`-free graph of minimum degree at least three contains a
power-of-two cycle.

This is the only authored axiom in the framework and external example
packages. `tools/lint_automation_first.py`, `tools/verify_lean.py`, and
`tests/test_repository.py` allow exactly this declaration at exactly its
graph-level module path. Every other axiom, admission, or unsafe declaration
is rejected.

### Erdős execution and provenance

`runP13FreeCT1` reaches

```text
entry → equivalenceCertification → realizationDecision → avoidingTerminal
```

with zero checks. `hssTarget_of_p13Free` converts its semantic residual to
the packed power-of-two-cycle target, and `p13FreeBranch_closed` contradicts
the existing `ctx.avoids`. Consequently `inducedP13_of_hss` proves the exact
realization required by `cor:p13-exists`.

For any resulting embedding, `runInducedP13CT1` reaches

```text
entry → equivalenceCertification → realizationDecision → c1Terminal
```

with one local certificate check. The application exports its semantic
theorem, totality, exact trace, and polynomial work theorem.

`verifiedInducedP13Prefix` consumes a concrete
`VerifiedBoundariedReplacementPrefix`; `inducedP13Prefix_previous` recovers
that exact input, while `inducedP13Prefix_stage` and
`inducedP13Prefix_realization` expose the new CT1 output. The endpoint
`exists_verifiedInducedP13Prefix` starts with only the official internal
object, baseline, and target avoidance.

## Node `[17]` and packing clauses of `[25]`–`[27]`: one CT12 stage

The manuscript first defines `p₁₃` as the maximum size of a vertex-disjoint
induced-`P₁₃` family, then uses maximality to make its complement
`P₁₃`-free. The implementation selects a maximum family, so both statements
come from the same object.

### Reusable core and CT12 profile

`Core.FiniteDisjointPacking.Profile` takes a finite item type, a finite vertex
schedule, one finite support per item, and a representative vertex in each
support. The framework proves:

- existence of a maximum-cardinality pairwise-disjoint family;
- maximum implies maximal saturation;
- the selected list is duplicate-free and pairwise support-disjoint;
- every other disjoint list is no longer; and
- the selected list has length at most the host vertex count, by injectivity
  of the representative map.

The maximum is selected by proof-level finite choice. No executable
definition constructs `Finset.univ` of embeddings or a powerset of packings.
`CT12.DisjointPacking.Profile.run` passes only the selected list to the
existing well-founded `CT12.ListPeeling` runner. The framework exports the
exhausted terminal, valid typed trace, totality, exactly `pₖ` iterations, at
most `n` iterations, and trace length at most `4n + 3`.

### Reusable graph layer

`Graph.InducedPathPacking` instantiates finite supports with literal Mathlib
embeddings `pathGraph k ↪g G`. It proves:

- maximum and maximal induced-path packing theorems;
- exact support size `k` for every window;
- `|W| = k pₖ`, `|R| + k pₖ = |V(G)|`, and `k pₖ ≤ |V(G)|`;
- construction of `R` as an actual `FiniteObject` induced on the vertex
  complement; and
- induced-`Pₖ`-freeness of `R` and every induced subgraph of `R`.

`Graph.FiniteObject.induceFinset` owns the reusable finite induced-subgraph
construction and canonical embedding. `Graph.FiniteObject.InternalSubgraph`
represents an arbitrary finite graph supported inside the host, and the graph
layer proves that replacing it by the induced graph on the same support cannot
lower minimum degree. The HSS module therefore proves the reusable exact
consequence that a finite `P₁₃`-free graph avoiding power-of-two cycles
contains no finite internal subgraph of minimum degree at least three.

### Erdős execution and provenance

`Erdos64EG.Internal.p13` is the selected maximum cardinality,
`p13CoveredVertices` is `W`, and `p13Remainder` is the actual induced graph
`R`. The application exports `p13_maximum`, `p13_saturated`,
`runP13PackingCT12_iterations_exact`, `p13Remainder_partition`,
`thirteen_mul_p13_le_vertexCount`,
`p13Remainder_free`, `p13Remainder_componentwise_free`, and
`p13Remainder_internalSubgraphThreeCore_free`.

`verifiedP13PackingPrefix` consumes the exact `VerifiedInducedP13Prefix`.
Its generic graph prefix derives packing nonemptiness from the induced
embedding retained by CT1, rather than accepting nonemptiness or a packing as
an input. `p13PackingPrefix_previous` recovers the exact predecessor, and
`exists_verifiedP13PackingPrefix` starts only from the official internal
graph, baseline, and target-avoidance hypotheses.

## Node `[18]`: one exhaustive attachment-label CT10 stage

The manuscript fixes an induced path `v₀…v₁₂` and assigns each outside
vertex its set of adjacent path positions. A nonempty label is legal exactly
when no two selected positions differ by `2` or `6`, since those differences
close cycles of length `4` or `8`.

### Reusable CT10 and core layer

`CT10.ExhaustiveClassification.Profile` takes an explicitly enumerated
candidate type and a decidable acceptance predicate. Its accepted subtype is
the exact class table. The profile constructs and executes the canonical CT10
capability, whose rows contain their own accepted class, and proves:

- the exhaustive terminal;
- the exact trace
  `entry → table → direct → missing → exhaustiveTerminal`;
- semantic outcome validity and typed-trace validity;
- totality with the exact terminal and trace; and
- a quadratic budget for candidate classification, direct scanning, and row
  population.

The work ledger is

```text
candidateCount + classCount + classCount².
```

`Core.Enumeration.subtype` retains the source order and constructs its
accepted enumeration directly from the already duplicate-free filtered list.
It does not perform a second quadratic deduplication pass.

### Reusable graph layer

`Graph.InducedPathAttachment` owns all path-attachment semantics independent
of the Erdős constants:

- `Label order`, `LabelCode order`, exact bit-code encode/decode equivalence,
  and the sequential `2^order` code enumeration;
- symbolic `and_shift_eq_zero_iff_no_gap`, proving for any positive gap that
  a shifted bit intersection is zero exactly when the decoded label has no
  pair at that gap, without enumerating the code universe;
- `Legal`, `Compatible`, `C`, and `omegaTwo`, with exact zero/one semantic
  theorems;
- construction of the literal path segment and the simple cycle closed by two
  attachments of one outside vertex; and
- `attachmentLabel_legal_of_avoids` and its finite-object wrapper, proving
  that target avoidance places every actual nonempty attachment in the legal
  class table.

`Graph.PackedMinimumDegreeCycle.
EdgeRootedBoundariedInducedPathPackingAttachmentPrefix` is the framework-owned
composition of the preceding CT12 packing prefix and a proved attachment
classification. It keeps the exact predecessor, stores the complete CT10
`VerifiedStage` on the inherited branch context, and exposes legality and
acceptance for every actual path attachment. This is ordinary typed theorem
composition; no residual route is involved.

### Erdős execution and provenance

`P13CodeLegal` is the constant-width bit test

```text
code ≠ 0,
code AND (code >> 2) = 0,
code AND (code >> 6) = 0.
```

`p13CodeLegal_iff_gapLegal` derives its manuscript semantics from the generic
symbolic gap theorem. `p13Legal_iff_gapLegal` separately proves equivalence to
the graph-level cycle predicate. The bounded local computations certify:

- `p13Label_candidate_count`: `8192` candidates;
- `p13LegalLabel_count`: `399` accepted labels;
- `p13LegalLabel_size_distribution`: `13,60,122,122,63,17,2` for sizes
  `1,…,7`;
- `legalP13Label_card_bounds`: every accepted label has size from `1` to `7`;
  and
- `p13Label_check_count`: exactly `167792` accounted checks.

`p13Label_checks_quadratic` states the concrete candidate-square bound used
by the generic profile.

The fixed computation is isolated behind two modules. `P13LabelKernel`
contains only the thirteen-bit definitions and CT10 profile, while
`P13LabelCertificate` contains every `native_decide` proof. The latter imports
no Erdős proof stage after `InternalProblem`, so edits to CT1, CT2, CT3, CT12,
CT10 graph integration, tests, or later manuscript stages reuse its cached
`.olean`. `CT10P13LabelAlgebra` contains no finite reflection and transports
only the cached certificate facts into the graph-semantic proof.

`runP13LabelCT10_terminal`, `runP13LabelCT10_trace`, and
`runP13LabelCT10_total` expose the exhaustive execution, including semantic
validity and typed-trace validity. `p13C`, `p13C_eq_one_iff`, `p13OmegaTwo`,
and `p13OmegaTwo_eq_one_iff` are the exact fixed-order, power-of-two
instantiations of the manuscript relations.

`verifiedP13LabelAlgebraPrefix` consumes a concrete
`VerifiedP13PackingPrefix`. `p13LabelAlgebraPrefix_previous` recovers that
exact input, and `p13LabelAlgebraPrefix_stage` exposes the CT10 verification
package. `p13AttachmentLabel_legal` derives actual-label membership from the
existing target-avoidance proof, and `p13AttachmentLabel_accepted` transports
that result into the compact accepted-class contract. The endpoint
`exists_verifiedP13LabelAlgebraPrefix` starts only from the official internal
object, baseline, and target avoidance, and retains every earlier stage on
the same selected graph.

## Independent transfer

`examples/even_cycle/EvenCycleExample/CT2Audit.lean` instantiates the exact
`Graph.PackedMinimumDegreeCycle` and `CT2.CertifiedReductionInput` APIs with
the textbook even-cycle target. It exports:

- `exists_noProperCorePrefix`;
- `properCoreCT2Run_terminal`;
- `properCoreCT2Run_trace`;
- `properCoreCT2Run_checks`; and
- `properSubgraph_minDegree_le_two`.

The same package also instantiates the fixed-vertex local-deletion route and
its degree-three endpoint theorem. Reusable rank, subgraph, cycle transport,
runner, totality, and work-bound proofs live in the framework.

`EvenCycleExample.CT3SeriesReduction` supplies the independent textbook
Duffin parity-series coordinate model and additionally constructs
`exists_duffinConcreteBoundariedReplacementStage` at boundary `Fin 2`, using
the same literal packed-graph stage. This is the non-Erdős transfer
fixture for the local-to-global gluing theorem.

`examples/even_cycle/EvenCycleExample/CT1InducedEdge.lean` independently
instantiates the exact `Graph.InducedPath.Profile`. It proves the textbook
fact that every selected graph edge is an induced `P₂`, executes the same
certificate-driven runner, and exports its C1 terminal, exact trace, semantic
theorem, totality, one-check polynomial bound, and a concrete `K₄` execution.

`examples/even_cycle/EvenCycleExample/CT12MaximalMatching.lean`
independently instantiates the new `Graph.InducedPathPacking` profile at
`k = 2`. Its selected windows are a maximum matching, its CT12 run reaches
the exhausted terminal in exactly the matching-number many iterations with
the same vertex-linear bounds, the exact
partition is `|R| + 2p₂ = |V|`, and maximal saturation proves that the
unmatched remainder is edgeless.

`examples/mantel/MantelExample/CT10EdgeAttachment.lean` independently
instantiates the exact compact-label and CT10 profile for the textbook local
step in Mantel's theorem. An induced edge has four possible attachment labels
and exactly two legal nonempty labels, both singletons. The package proves
candidate count `4`, class count `2`, check count `10`, the exhaustive
terminal and exact typed trace, and singleton cardinality. Mathlib's
`is3Clique_iff_exists_cycle_length_three` converts `CliqueFree 3` into the
cycle-avoidance premise of the shared graph theorem, so every actual nonempty
attachment to the edge is accepted by the same classification contract.

## Validation

The following checks pass on 2026-07-13:

```text
make lint
  OK: CT1–CT17 expose only automation-first canonical APIs

make framework-build
  Build completed successfully (3238 jobs)

lake build Erdos64EG.CT10P13LabelAlgebra Erdos64EG.Tests \
  Erdos64EG.WebExport
  Build completed successfully (3205 jobs)

lake build MantelExample
  Build completed successfully (3065 jobs)

make generate
  Framework build completed successfully (3238 jobs)
  Even-cycle build completed successfully (3135 jobs)
  Erdős build completed successfully (3099 jobs)
  Greedy-coloring build completed successfully (1303 jobs)
  Mantel build completed successfully (3065 jobs)
  Rendered 4 compiled Lean examples
  Rendered 17 tactic projections and 5 generated routes

python3 tools/verify_lean.py
  Kernel checked 17 automation-first tactics, 124 nodes, 108 typed edges,
  36 residual kinds,
  5 routes, and 4 compiled examples

make validate
  OK: 17 automation-first Lean tactics, 124 nodes, 108 typed edges,
  36 residual kinds,
  5 generated routes, 0 manual node obligations

UV_CACHE_DIR=/tmp/uv-cache uv run --offline \
  --with-requirements requirements.txt python -m pytest -q
  35 passed in 3.27s

git diff --check
  passed
```
