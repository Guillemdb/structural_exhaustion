# Structural Exhaustion Graph Layer API

Status: target architecture. This document specifies the clean-break target
for `StructuralExhaustion.Graph`; it does not claim that all proposed Lean
declarations already exist.

## 1. Objective

The Graph layer gives graph-theoretic semantics to the domain-independent API
in `DOMAIN_INDEPENDENT_CORE.md`. It must be a thin specialization, not a second
proof engine. Core owns coordinate-path composition, replacement execution,
finite decisions, ledger updates, CT transitions, routing, and closure. Graph
owns only the meaning and laws of finite graph objects, graph coordinates,
boundaries, gluing, graph observables, and graph targets.

The intended application shape is:

```lean
noncomputable def nextNode :=
  Graph.ctExecutor previousResidual localGraphCertificate
```

The node supplies its literal predecessor and the one new mathematical fact.
It does not construct a successor state, copy an inherited theorem, select a
route, or assemble a replacement graph.

This API has a clean-break compatibility policy. Deprecated application-shaped
Graph records do not receive wrappers or aliases. Reusable semantics move to
their canonical owner, and applications are updated to instantiate that owner
directly.

## 2. Package boundary

The target dependency direction is:

```text
StructuralExhaustion.Core    Mathlib.Combinatorics.SimpleGraph
             \                            /
              v                          v
                StructuralExhaustion.Graph
                            |
                            +-- Graph.External
                            |
                            +-- reusable graph theorem profiles
                            |
                            v
               proof applications, including proofs.erdos_64_eg
```

Core contains no graph vocabulary. Graph contains no theorem-specific branch
names, target lengths, fan types, paper labels, or application routes. An
application may import Graph and an explicit external graph theorem, but Graph
must never import an application proof.

## 3. Irreducible graph object

Coordinate changes can alter the vertex type. The canonical ambient object is
therefore existentially packed rather than fixed to one global vertex type:

```lean
structure FiniteObject where
  Vertex : Type u
  graph : SimpleGraph Vertex
  vertices : FinEnum Vertex
  decideAdj : DecidableRel graph.Adj
```

This is the conceptual public form of the existing packed finite object. It
contains only the mathematical graph and the deterministic finite schedule
needed by executable CTs. It does not contain:

- a target predicate;
- minimum-degree or target-avoidance assumptions;
- a selected root, path, fan, or decomposition;
- a residual or ledger;
- a progress measure; or
- a route or closure certificate.

Fixed-vertex `FiniteObject V` views may remain internal conveniences when no
coordinate changes occur. They are not a second ambient representation.

From the packed object, Graph derives once and for all:

- ordered vertices, neighbours, edges, and darts;
- cardinality, degree, minimum degree, maximum degree, and edge count;
- adjacency and membership decision procedures;
- canonical subtype enumerations for induced supports; and
- isomorphism transport for every derived invariant.

No application registers these derived operations as fields.

## 4. Minimal graph problem registration

The minimum theorem-level registration is a Core problem whose ambient type is
the packed finite object. No `GraphProblemProfile` wrapper is needed:

```lean
def Graph.problem
    (Baseline : Graph.FiniteObject -> Prop)
    (BranchState : Graph.FiniteObject -> Type uState) : Core.Problem where
  Ambient := Graph.FiniteObject
  Baseline := Baseline
  BranchState := BranchState
```

The target remains a separate predicate:

```lean
variable (Target : Graph.FiniteObject -> Prop)
```

This separation is required. The same graph class may be searched for a cycle,
an induced path, a coloring, a minor, or an obstruction response without
redefining the ambient model.

`BranchState` contains only irreducible theorem state that is meaningful for
the current ambient graph. Selected occurrences, CT outputs, classifications,
and inherited facts belong to the Core residual ledger, not to a growing
application record.

Optional capabilities are registered separately:

| Capability | Supplied only when needed |
|---|---|
| `Core.Progress` | A well-founded graph order and its strictness theorem |
| `Graph.isomorphismEquivalence` | Canonical `Core.SemanticEquivalence` for packed finite graphs |
| `Graph.TargetInterface` | Isomorphism invariance and local response reflection |
| `Graph.Locality` | Supports, boundaries, and exact induced restriction laws |
| `Graph.BoundaryAssembly` | Piece/context ownership and reconstruction |
| `Core.ResourceBudget` | Cardinality, charge, degree, rank, or multiplicity resource |
| `Graph.ObstructionTransport` | Preservation of the current obstruction by a primitive graph coordinate |

A theorem that only performs a finite CT1 target check needs none of the
replacement, budget, or compactness capabilities.

## 5. Graph coordinate system

Graph instantiates `Core.CoordinateSystem` with the following primitive
generators:

```text
induce | root | relabel | deleteVertex | deleteEdge | contract | replacePiece
```

Packing and unpacking are representation operations, not mathematical
coordinates. A path of graph coordinates is constructed and run only by Core.

### 5.1 Primitive semantics

For each supported generator, Graph proves the generic graph laws:

- the exact source and target graph;
- adjacency reflection or the declared adjacency transformation;
- finite-enumeration compatibility;
- graph-isomorphism naturality;
- support and boundary transport; and
- exact vertex-count and edge-count changes when defined.

The theorem profile supplies only laws that depend on its baseline, target, or
retained obstruction:

- baseline preservation;
- target-response naturality;
- retained-obstruction transport; and
- strict decrease for the registered `Core.Progress`, if used.

Core derives identity, composition, ledger transport, and exact predecessor
handoff. An application cannot manually relabel an output, run two coordinate
changes in sequence, or copy proofs from the pre-coordinate graph.

### 5.2 Restriction and recentering

Graph recentering means selecting a root, oriented edge, boundary tuple, or
marked support through a Core-owned coordinate stage. It does not require a
new graph if the underlying adjacency is unchanged. Restriction is an induced
subgraph on the support carried by the incoming residual. The framework owns
the subtype vertex type, embedding, and transported ledger.

The application supplies the selected parameter only when it is genuinely new
semantic evidence. A CT-selected root or support is retrieved from the
predecessor ledger and is never selected again by local code.

## 6. Local atoms, contexts, and gluing

Graph locality is based on a finite support and its labelled interface with the
outside graph.

```lean
structure BoundaryPiece where
  Boundary : Type uBoundary
  Internal : Type uInternal
  boundaryVertices : FinEnum Boundary
  internalVertices : FinEnum Internal
  graph : SimpleGraph (Sum Boundary Internal)
  decideAdj : DecidableRel graph.Adj

structure OutsideContext (Boundary : Type uBoundary) where
  Internal : Type uOutside
  graph : SimpleGraph (Sum Boundary Internal)
  noBoundaryEdge : forall left right,
    Not (graph.Adj (.inl left) (.inl right))
```

The piece owns boundary-to-boundary edges. The normalized outside context owns
all remaining outside edges. This convention makes the edge ownership
disjoint and reconstruction exact.

`Graph.BoundaryAssembly` instantiates `Core.AtomContextAssembly` over
`Graph.isomorphismEquivalence` with:

- a labelled boundaried piece as the atom;
- the normalized outside graph as the context;
- equality of boundary labels and any declared interface code as
  compatibility;
- boundaried graph union as assembly; and
- a graph isomorphism from the assembly to the incoming ambient graph as the
  reconstruction law.

The existing `Graph.PackedBoundariedGluing` contains the graph mathematics for
this adapter. Graph continues to own embeddings, edge ownership, reconstruction
isomorphisms, degree preservation, and exact size change. Core owns:

- replacement execution;
- compatibility lookup;
- assembly invocation;
- target-response comparison;
- strict-progress verification;
- ledger extension; and
- routing to closure or the exact complementary residual.

An application cannot expose a `glue`, `handoff`, `replacementOutput`, or
`routedResult` declaration.

## 7. Interfaces and exact responses

A boundary interface is the smallest code through which compatible outside
contexts can affect the target. It may record boundary adjacency, degrees,
parity, connectivity, attachment roles, or a finite target-response vector.
The code is target-relative and is not a universal property of a graph piece.

```lean
structure TargetInterface (Target : Graph.FiniteObject -> Prop) where
  isomorphismInvariant : Core.TargetInvariant
    Graph.isomorphismEquivalence Target
  InterfaceCode : Type uCode
  code : BoundaryPiece -> InterfaceCode
  Outside : Type uOutside
  compatible : BoundaryPiece -> Outside -> Prop
  targetResponse : BoundaryPiece -> Outside -> Prop
  reflectAssembly : ...
```

For executable CT3 and CT7 use, the residual supplies an exact finite response
coordinate family and a symbolic coverage theorem. The outside context type
need not itself be finite. Core scans only the declared finite code family and
uses coverage to lift equality back to every compatible context.

The following algebra is domain-independent and belongs in Core:

- two representatives and their progress increment;
- finite response vectors;
- exact response-table comparison;
- distinction versus universal neutrality;
- target-complete response equivalence; and
- conditional orientation after nonzero progress.

Accordingly, the generic content currently named
`Graph.FiniteContextResponseComparison` and
`Graph.FiniteSameInterfaceExchange` moves to canonical Core response modules.
Graph retains only constructors proving that graph boundary codes and glued
targets instantiate those Core contracts.

## 8. Finite extraction and packing

Graphs do not need continuum compactness for ordinary finite CT execution.
They do need exact residual-owned extraction profiles:

- induced restriction to a selected support;
- greedy disjoint packing of supplied occurrences;
- connected-component or block extraction;
- role-homogeneous fibre extraction;
- canonical path, tree, matching, or separator selection; and
- a finite representative of an isomorphism or response class.

The combinatorial algorithms are generic Core operations whenever they inspect
only an ordered finite family, labels, capacities, or relations. Graph owns
the bridge showing that the selected items are graph occurrences and that
their supports or interfaces have the claimed meaning.

For example, role-homogeneous extraction is CT9 finite-fibre overload in Core.
The fact that a role describes a graph incidence belongs to Graph or the
application; the pigeonhole theorem does not.

No machine may enumerate an implicit class of all finite graphs or all outside
contexts. Every finite scan is over an explicit family in the incoming
residual, and every universal outside-context statement is discharged by a
symbolic coverage theorem.

## 9. Graph budgets and progress

Graph uses two independent Core facilities.

### 9.1 Structural progress

Typical `Core.Progress` instances are:

- vertex count;
- edge count;
- lexicographic internal-vertex and local-edge count;
- support size;
- number of unresolved occurrences; and
- a finite branch rank supplied by the manuscript.

Graph proves how primitive deletion, contraction, restriction, or replacement
changes these measures. Core owns the well-founded contradiction with
minimality.

### 9.2 Mathematical resource budgets

Typical `Core.ResourceBudget` instances are:

- degree deficit or surplus;
- charge and correction terms;
- available vertices, edges, ports, or labels;
- support mass and overlap multiplicity;
- response rank; and
- target-length or compatibility capacity.

The application supplies the exact graph inequality connecting its local
quantity to the target. Core owns assignment, summation, fibre counting,
capacity comparison, and the resulting route.

The polynomial verifier-work budget remains separate from every mathematical
resource budget.

## 10. Automatically derived graph profiles

The framework should derive as much as possible from a small collection of
semantic registrations.

| Registered primitive | Automatically derived by Graph/Core |
|---|---|
| Packed finite graph | Ordered vertex, edge, dart, and neighbour scans |
| Induced-support semantics | Restricted object, embedding, nested restriction, support transport |
| Graph isomorphism laws | Relabeling paths and invariant transport |
| Boundary ownership and reconstruction | Compatible gluing and local replacement execution |
| Target reflection on assembly | CT3 response comparison and CT7 distinguishing-context routing |
| Progress effect | CT2 minimality closure and CT12 well-founded peeling |
| Label and capacity functions | CT4 assignment, CT9 overload, and CT14 aggregation |
| Ordered occurrence family | CT6 first failure, CT8 repetition, and CT10 classification |
| Rank coordinates | CT15 target-relative quotient and full-rank ledger |
| Bounded target parameters | CT17 thickening and survivor arithmetic |

The following cannot be derived from a bare graph and must be proved once by
the relevant reusable profile or theorem application:

- that a baseline survives a coordinate change;
- that a local interface is complete for the chosen target;
- that a replacement is admissible and strictly smaller;
- that a target obstruction survives restriction or extraction;
- that a charge, degree, or multiplicity inequality holds; and
- that a terminal graph configuration realizes the target or contradicts the
  baseline.

These are semantic certificates, not new state objects or routing code.

## 11. CT1-CT17 graph responsibilities

All executors are the Core executors described in
`DOMAIN_INDEPENDENT_CORE.md`. Graph exports canonical constructors for their
graph semantic inputs.

| CT | Graph responsibility |
|---|---|
| CT1 | Validate an explicit cycle, path, coloring, clique, minor, or other target witness, or retain exact target avoidance |
| CT2 | Delete, contract, induce, or replace a piece and use strict graph progress or emit the exact criticality residual |
| CT3 | Compress a boundaried piece by its exact response in every compatible graph context |
| CT4 | Assign graph demands to eligible vertices, edges, ports, labels, or other finite resources and compare capacity |
| CT5 | Aggregate local graph witnesses, contributions, charges, or support deficits into one ledger account |
| CT6 | Select the first inactive site or failed condition in an ordered residual-owned graph schedule |
| CT7 | Produce a distinguishing outside context or certify universal response neutrality |
| CT8 | Detect a repeated exact graph/interface type and compare the two responses or certify no repetition |
| CT9 | Detect an overloaded label or role fibre in a supplied finite graph family |
| CT10 | Exhaust an attachment, incidence, separator, local type, or other declared finite graph classifier |
| CT11 | Localize a negative additive graph budget to a vertex, edge, dart, support, or supplied component |
| CT12 | Peel vertices, edges, blocks, components, supports, or occurrences with well-founded decrease and restoration |
| CT13 | Use a primary graph resource and then the canonical fallback, including payer, port, or replacement tiers |
| CT14 | Compare aggregate graph mass with label, support, overlap, multiplicity, or capacity bounds |
| CT15 | Compute boundary-response, admissible-quotient, support, or target-determination rank |
| CT16 | Exhaust the complete finite support and compare its closed graph/interface code with the target code |
| CT17 | Exhaust bounded target lengths, offsets, scales, shells, compatibility windows, or survivor parameters |

Graph does not define a route from one CT to another. Cross-CT transitions are
registered and executed in Core/Routes and consume the full predecessor
ledger.

## 12. Reusable graph theorem profiles

The Graph package may contain theorem profiles that are useful across many
applications, provided they are built entirely from the public graph adapter
and Core CTs. Examples include:

- path, walk, cycle, clique, coloring, and minor target encodings;
- induced-subgraph and edge-deletion preservation lemmas;
- minimum-degree cycle extraction;
- degeneracy peeling and greedy coloring;
- Mantel-type negative-budget localization;
- boundaried replacement and rank-drop theorems; and
- matching, packing, component, and separator profiles with no fixed paper
  constants.

These are reusable clients of the Graph API, not fields of the graph problem
constructor.
`MinimumDegreeCycle`, `GreedyColoring`, and `Mantel` therefore demonstrate the
layer but do not enlarge its minimum public registration surface.

## 13. Application boundary for Erdos--Gyarfas

The following concepts are specific to the current Erdos--Gyarfas proof and
must not occur in the generic Core or Graph API:

- `P13` and fixed 13-position windows;
- quarter-credit or theorem-specific curvature formulas;
- fans, fan centers, fan shoulders, and fan-closed pairs;
- open, high, separator, or completion ports;
- Type A and Type B coordinates;
- D1, D3, D4, D5, and D7 clause names;
- hot/cold, germ, long-prefix, and cold-skeleton branch names;
- theorem-specific surplus patterns and target-length sets; and
- node numbers or paper branch identifiers.

These objects belong under `proofs/erdos_64_eg` or a dedicated
`StructuralExhaustion.Applications.Erdos64EG` namespace. Their implementation
may define local predicates and prove semantic certificates, but every state
transition must be a direct Graph/Core executor invocation on the predecessor
residual.

A generic notion such as finite support, labelled boundary, local incidence,
role fibre, charge, or response coordinate remains in Core or Graph. The
Erdos--Gyarfas module supplies the particular support size, labels, roles,
weights, target predicate, and local lemmas.

## 14. Current-module ownership migration

The clean target classifies the current modules by mathematical ownership.

| Current kind | Target owner |
|---|---|
| `Core.ResidualRefinement`, `Core.CTTransition`, finite ledgers, searches, capacities, ranks | Core |
| Generic parts of `FiniteContextResponseComparison` and `FiniteSameInterfaceExchange` | Core response algebra |
| Generic role-fibre and ordered-family extraction | Core CT9/CT10/CT12 machinery |
| `Basic`, packed `FiniteObject`, `InducedSubgraph`, edge deletion/contraction, graph isomorphism transport | Graph primitive semantics |
| `PackedBoundariedGluing`, graph boundary ownership, degree preservation, graph target reflection | Graph assembly adapter |
| Paths, cycles, coloring, Mantel, minimum-degree, matching, generic separator theorems | Reusable Graph theorem profiles |
| `P13*`, `Fan*`, `PortShoulder*`, `TypeA*`, `TypeB*`, `Surplus*`, D-clause, long-prefix, and cold-branch modules | Erdos--Gyarfas application |
| `Graph.External.*` | Explicit graph-theorem trust boundary |

Moving a declaration does not justify copying it into both locations. The old
namespace is removed after its clients use the canonical owner.

## 15. Explicit theorem import boundary

Core and the generic Graph layer remain axiom-free. A graph theorem used as a
black box is isolated under `StructuralExhaustion.Graph.External` with:

- a stable source identifier;
- the exact local hypotheses;
- the exact conclusion;
- isomorphism and coordinate compatibility;
- retained-obstruction consequences, when relevant; and
- no route, node output, or final application theorem in its contract.

For example, a Hegde--Sandeep--Shashank theorem may be imported as one named
graph theorem. It cannot be encoded as an axiom asserting that the whole
Erdos--Gyarfas residual closes. Replacing the external theorem with a formal
proof must not change the Core executor or application-node API.

## 16. Ledger and failure semantics

Every graph executor reads inherited facts through `Core.LedgerQuery` and
extends the same residual state. Typical registered stages include:

- target avoidance;
- selected support or occurrence;
- baseline preservation under the active coordinate path;
- boundary and response completeness;
- deletion or replacement criticality;
- charge, multiplicity, and rank ledgers;
- target witness validation; and
- an explicit external theorem contract.

The Graph layer treats the following as typed residuals rather than
assumptions or exceptions:

- target witness validation failed;
- no admissible deletion or smaller replacement;
- boundary profile mismatch;
- a distinguishing outside context;
- missing target-response coverage;
- obstruction transport failed;
- a demand has no payer or a fibre is overloaded;
- a local budget is negative;
- a rank or whole-support code differs; and
- a bounded target parameter survives every checked case.

Each residual has a registered downstream CT consumer or remains an explicit
active frontier. No application may erase it by constructing a custom output.

## 17. Forbidden public surface

Neither Graph nor a graph application may expose fields for:

- a selected CT outcome or route;
- a manually extended or copied ledger;
- a transformed predecessor graph produced outside a Core coordinate path;
- a glued successor or replacement handoff;
- a duplicate target-avoidance or baseline record;
- an application-defined closure status;
- an implicit enumeration of all graph contexts;
- a theorem-specific constant in a generic Graph profile; or
- an unnamed fallback proposition with no residual consumer.

If repeated application code needs such an operation, it indicates missing
Core machinery or a missing graph semantic adapter.

## 18. Thin application criterion

A compliant boundaried replacement node has this conceptual form:

```lean
noncomputable def replacementNode :=
  Graph.BoundaryReplacement.advance previousResidual
    boundarySemantics
    localReplacementCertificate
```

The application does not mention the outside context, graph sum type,
embedding, gluing isomorphism, composed coordinate path, target-response scan,
minimality contradiction, residual constructor, ledger extension, or route.
Graph supplies the graph semantics and Core performs all execution.

The Graph API is complete when reusable examples and every Erdos--Gyarfas node
can use this shape, while the Navier-Stokes rows in `PDE_LAYER_API.md` use the
same Core residual, ledger, coordinate, assembly, CT, and routing contracts.
