# EG Hypostructure Expansion Plan

This document is the expansion inventory for porting legacy Erdős–Gyárfás nodes to
the Hypostructure framework.

## Sources (authoritative)

- `migration/hypostructure/eg-node-matrix.csv`
- `migration/hypostructure/api-feature-matrix.csv`
- `examples/erdos_64_eg/Erdos64EG/Node*.lean` (legacy reference implementations)
- `examples/hypostructure_erdos_64_eg/HypostructureErdos64EG` (new Hypostructure target)

## Design rule for all nodes

Node implementations must only use:

- predecessor residual
- predecessor accumulated ledger
- framework transition/progress APIs

No node module should copy predecessor payload manually, define problem-specific
routing, or introduce dedicated transport data. All handoff and branch routing must
be owned by the framework transition/decision/focus machinery.

## Required feature set currently visible in `eg-node-matrix.csv`

The table below lists every required feature id appearing in `required_features`
across legacy nodes, the owner, current `api-feature-matrix` status, and the node
IDs that consume it.

| feature id | owner | status | implementation module | consuming nodes | notes |
|---|---|---|---|---|---|
| `core.closure` | Core | kernel_checked | `Hypostructure.Core.Closure` | 3, 7 | Active / terminal split |
| `core.decision` | Core | kernel_checked | `Hypostructure.Core/Residual/Decision.lean` | 2 | Dependent both-branch decision structure |
| `core.focus-selection-work` | Core | kernel_checked | `Hypostructure.Core/Residual/Focus.lean` | 4, 5, 6, 8, 9, 10 | Focus + work budget selector contracts |
| `core.progress` | Core | kernel_checked | `Hypostructure.Core.Progress` | 4, 8 | Well-founded residual progress |
| `core.proof-projection` | Core | kernel_checked | `Hypostructure.Core/Residual/ProofProjection.lean` | 12, 13, 14 | Zero-claim projections and focused projection certificates |
| `ct.ct1` | CT | kernel_checked | `CT1/Automation.lean` | 6, 7, 15, 16, 96, 98, 100, 155 | First residual-owned target-realization stage |
| `ct.ct10` | CT | kernel_checked | `CT10/Automation.lean` | 18, 21, 130 | Finite-table classifier |
| `ct.ct11` | CT | kernel_checked | `CT11/Automation.lean` | 61 | First finite overlap/defect profile |
| `ct.ct12` | CT | kernel_checked | `CT12/Automation.lean` | 17, 102 | Maximal packing / maximality-termination workflows |
| `ct.ct15` | CT | kernel_checked | `CT15/Automation.lean` | 31, 32, 33, 34, 35, 36, 37, 38, 40, 41, 43, 44, 45, 46, 47 | Matrix/rank/targeted branch workflows |
| `ct.ct2` | CT | kernel_checked | `CT2/Automation.lean` | 67 | First criticality-style finite deletion |
| `ct.ct3` | CT | kernel_checked | `CT3/Automation.lean` | 39, 42, 104 | Coordinate class/exact-context family |
| `ct.ct6` | CT | kernel_checked | `CT6/Automation.lean` | 127, 128, 153 | Ordered activity / overload seed extraction |
| `ct.ct7` | CT | kernel_checked | `CT7/Automation.lean` | 140, 142, 143 | Contextual response split |
| `ct.ct9` | CT | kernel_checked | `CT9/Automation.lean` | 137 | Exact finite class overload |
| `graph.atom-replacement` | Graph | kernel_checked | `Graph/Replacement.lean` | 13, 14 | Overlap-aware atom replacement |
| `graph.atom-response-coordinates` | Graph | kernel_checked | `Graph/AtomResponse.lean` | 12, 14 | Response-coordinate constructors |
| `graph.boundaried-atom-profile` | Graph | kernel_checked | `Graph/BoundariedAtom.lean` | 11, 12 | Boundaried atom profile and constructor |
| `graph.boundary-overlap` | Graph | kernel_checked | `Graph/BoundaryOverlap.lean` | 13 | Boundary overlap audit and correction |
| `graph.ct1` | Graph | kernel_checked | `Graph/CT1.lean` | 6, 7, 96, 98, 100 | Graph-facing CT1 wrapper |
| `graph.ct10` | Graph | kernel_checked | `Graph/CT10.lean` | 130 | Graph-facing CT10 wrapper |
| `graph.ct12` | Graph | kernel_checked | `Graph/CT12.lean` | 102 | Graph-facing CT12 wrapper |
| `graph.ct2` | Graph | kernel_checked | `Graph/CT2.lean` | 67 | Graph-facing CT2 wrapper |
| `graph.ct3` | Graph | kernel_checked | `Graph/CT3.lean` | 104 | Graph-facing CT3 wrapper |
| `graph.ct6` | Graph | kernel_checked | `Graph/CT6.lean` | 127, 128 | Graph-facing CT6 wrapper |
| `graph.ct7` | Graph | kernel_checked | `Graph/CT7.lean` | 140, 142, 143 | Graph-facing CT7 wrapper |
| `graph.ct9` | Graph | kernel_checked | `Graph/CT9.lean` | 137 | Graph-facing CT9 wrapper |
| `graph.deletion-criticality` | Graph | kernel_checked | `Graph/DeletionCriticality.lean` | 9, 10 | Edge-deletion criticality |
| `graph.obstruction` | Graph | kernel_checked | `Graph/Obstruction.lean` | 15 | Induced obstruction registration/queries |
| `graph.progress` | Graph | kernel_checked | `Hypostructure.Graph.Progress` | 4 | Graph-owned strict progress proof flow |
| `graph.proper-subgraph-minimality` | Graph | kernel_checked | `Graph/Minimality.lean` | 8 | MDS and minimality transport |
| `graph.rooted-return` | Graph | kernel_checked | `Graph/RootedReturn.lean` | 5, 6, 7 | Edge-rooted return residuals |

## Legacy requirements not yet represented as `required_features`

These appear directly in legacy node code and must be lifted into generic
framework features before the legacy implementation can be eliminated:

- `Core.OrderThresholdSplit` (used by Node19, Node22): implemented as
  `Hypostructure.Core.OrderThresholdSplit`.
- `Core.FiniteBitRelationBarrier` (used by Node21): implemented as
  `Hypostructure.Core.FiniteBitRelationBarrier`.
- `Graph.InducedPathMaximalPacking` (used by Node17 and downstream Node21-using data flow):
  implemented as `Hypostructure.Graph.InducedPathMaximalPacking`.
- `Graph.InducedPathWindowLedger` (used by Node18/Node21/Node22 chain for near-cubic
  window accounting): implemented as `Hypostructure.Graph.InducedPathWindowLedger`.
- `Graph.SurplusClasswiseOverload` (used by Node19): implemented as
  `Hypostructure.Graph.SurplusClasswiseOverload`.
- `Core.FiniteTriangle` helper structure (currently used inside legacy barrier proofs):
  implemented as `Hypostructure.Core.FiniteTriangle`.

These features are now present in `hypostructure/Hypostructure/`, wired into
`Hypostructure.lean`, and recorded in `api-feature-matrix.csv`. They are still
abstract framework surfaces; EG-specific constants, obstruction length choices,
finite table rows, and numerical budgets belong only to the EG instantiation.

### Generic surfaces required by nodes 24--64

The later node family also requires the following domain-neutral contracts:

- `Core.ArithmeticTransport` for density complements, powered-capacity error
  restoration, and strict-gap normalization.
- `Core.FiniteEntropy` for entropy of a predecessor-owned finite state family.
- `Core.OneThreeRepair` for balance/handshake identities supplied by a domain
  adapter.
- `Core.Budget.Dynamic` for residual-indexed quantity-versus-limit budgets
  over ordered graph charges or PDE energy quantities.
- `PDE.Budget` for the PDE-facing umbrella over the Core dynamic-budget
  contract, reused for residual-indexed energies, fluxes, and other ordered
  analytic quantities.
- `Core.SupportSplit` for negative support localization and exhaustive
  high/low threshold splitting, predecessor-query projections, and the
  single ledger-producing stage node.
- `Core.Finite.OrderedPartition` for exact ordered label scans, member-set
  construction, coverage, disjointness, and linear work; Graph specializes it
  with induced connected components, while PDE contracts can use the same
  machinery for finite observable classes.
- `Core.Degradation` for guarded closure versus typed failed-guard residuals.
- `Graph.SupportComponents` for deterministic component partitions of a literal
  support, including the induced-component order, exact ambient support
  coverage, disjointness, and support-contained connectivity paths.
- `Graph.SupportCharge` for the graph-only degree projection into the
  generic support contract.
- `Core.AffineBalance` for the domain-neutral elimination step behind affine
  handshake/rank or defect/balance identities.
- `Graph.Budget` for the graph-facing umbrella over the Core dynamic-budget
  contract together with the support-charge and classwise-overload adapters.
- `Graph.Contraction` for the reusable finite contraction coordinate and the
  reduced vertex schedule it induces.
- `Graph.External` for exact-name local graph theorem contracts and reviewed
  allowlist entries at the graph trust boundary.
- `Graph.OneThreeRepair` for the finite-graph handshake and cycle-rank laws
  consumed by the Core affine-balance theorem.  PDEs should provide their own
  balance semantics and consume the same Core algebra rather than importing
  this graph adapter.

The Core entries are intentionally usable by PDE contracts as well as Graph
contracts.  Graph modules only derive graph observables; they do not own
branch routing or accumulated-ledger transport.

### Generic surfaces required by the cold branch (nodes 145--164)

The cold branch uses the same residual-owned schedule discipline.  Its Graph
surface is limited to induced-path support, external-incidence token
enumeration, branch-excess schedules, regularity decisions, and a corridor
contract whose stages are supplied by the problem contract.  The public
node-facing constructors are in `Graph/InducedPathColdQuery.lean`: they accept
typed `Core.Residual.Query` values and derive each schedule with `map` or
`dependentMap`.  They do not accept a detached window, copy a predecessor
object, or construct a route.

CT3 terminal evidence is exposed through `CT3/ScheduleWitness.lean`, and
same-interface packages are registered and retrieved through the generic
`Core/Response/SameInterface.lean` contract. Graph and PDE code supplies only
the witness or package interpretation; neither layer owns transport or
routing.

Core owns the event schedule split, first-failure scan, scale split, terminal
marker, and ledger extension.  Graph only supplies the finite graph
observables and the contract-owned corridor/path laws.  The same Core
schedule and residual APIs remain available to PDE contracts, where the item
runner can instead be a finite observable or local-tail schedule.

## Node scope checkpoints

### Already implemented in new folder
- Nodes 1-15 (ported and wired in `HypostructureErdos64EG.lean`).

### Target frontier requested in this phase
- Nodes 16-22: requires full lift of the missing core/graph modules above.
- The same mechanism should then be used for all remaining legacy nodes.

## Acceptance criteria for adding a new feature

1. Add feature module under `hypostructure/` with no problem-specific constants.
2. Add or update its record in `migration/hypostructure/api-feature-matrix.csv`
   with:
   - `feature_id`
   - stable `owner`
   - `new_module`
   - `status=kernel_checked` after bootstrap
3. Verify node port uses only:
   - predecessor stage type
   - accumulated ledger
   - framework constructors/continuations
4. Ensure no copy of predecessor route/ledger fields appears in the node module.
5. Register/update migration status for affected nodes and keep `generated` evidence
   refreshed.
