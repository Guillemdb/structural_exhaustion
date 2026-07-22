# EG Node 1 Migration Packet

Date: 2026-07-22

Status: direct implementation checked; semantic parity baseline pending

## Authority Snapshot

The sole mathematical and DAG authority is
`original_erdos_64_proof.tex`, pinned by
`migration/hypostructure/source-authority.json` at SHA-256
`215248521b7dbc6519076d506101b80a1c9a8425ee5c13b48a4ec52df21d2e10`.
The living proof is not an obligation source.

The frozen original statements are:

- diagram node `[1]`: `finite simple graph G` (original line 571);
- direct incoming edges: none;
- direct outgoing edge: unconditional `[1] -> [2]` (original line 596);
- nodes `[1]` through `[3]` jointly implement counterexample setup
  (original detailed-table line 1091);
- the counterexample predicate is minimum degree at least three and exact
  Mersenne-return avoidance on every oriented edge (original lines 1709-1716).

Node 1 introduces no mathematical assertion about the graph. The
minimum-degree certificate is an input of the official theorem carried in the
root residual for node 2; node 1 does not prove it. Target avoidance,
counterexample selection, and the first branch split belong to node 2.

## Mandatory Contract

| Field | Frozen value |
|---|---|
| Node ID | 1 |
| Literal predecessor | None; unique theorem root |
| Root inputs | Packed finite simple graph and theorem-supplied `minDegree >= 3` certificate |
| Inherited facts | None |
| Local responsibility | Install the exact theorem inputs in the unique accumulated ledger |
| New payload | None |
| Executor | `Hypostructure.Core.Residual.Ledger.initial` through `node1Counted` |
| Generated output | One framework-owned root residual stage |
| Outgoing consumer | Node 2 only |
| Complementary residual | None |
| Closure mechanism | None; node 1 is not a terminal branch |

The legal state flow is:

```text
InitialResidual
  -> Core.Counted.pure
  -> Core.Residual.Ledger.initial
  -> Node1Stage
  -> Node2
```

There is no query because there is no predecessor. There is no ledger
extension, route, branch selection, target predicate, copied output, or custom
handoff.

## Provision Boundary

| Input | Role | Reason |
|---|---|---|
| `InitialResidual.object` | definition | Literal finite graph supplied by the theorem invocation |
| `InitialResidual.baseline` | local certificate | Official minimum-degree premise, transported but not established by node 1 |

Framework-generated values are kept separate:

- `Ledger.initial` owns the root stage;
- `Counted.pure` owns the exact zero check count;
- `PolynomialCheckBudget.proofOnly` owns the polynomial envelope; and
- `node1Metadata` records the provision and generated-output boundaries with
  no manual obligation.

## Legacy Difference

The kernel-checked legacy `Erdos64EG.Internal.InitialResidual` also requires
`StrictGapAbsorption.LargeEnoughTail`. The immutable original does not grant
that premise at node 1, in the counterexample setup, or in the official
theorem. Hypostructure therefore does not copy or assume it.

Parity is intentionally normalized to the paper-visible graph, finite
schedule, edge/vertex counts, minimum degree, and baseline proposition. It
does not assert equality of legacy and Hypostructure residual records and does
not treat `largeEnoughTail` as paper content.

## Local Obligations

| Task | Declaration | Expected result |
|---|---|---|
| Root stage | `HypostructureErdos64EG.node1` | Literal input residual retained |
| Exact work | `node1Counted_checks_eq_zero` | Zero primitive inspections |
| Budget agreement | `node1Counted_checks_eq_budget` | Count equals registered budget |
| Work bound | `node1_work_bounded` | Core polynomial bound |
| Metadata | `node1MetadataComplete` | No manual obligations |
| Parity | `HypostructureParity.Erdos64EG.Node1.normalizedRootParity` | Same paper-visible root graph and baseline |
| Edge parity | `node1Edge_normalizedRootParity` | `[1] -> [2]` preserves normalized root data |

## Completion Gates

- Kernel: direct `HypostructureErdos64EG.Node1` build is fresh.
- Parity: direct normalized parity module kernel-checks, but the reviewed
  semantic parity field remains blocked until a clean baseline manifest is
  frozen.
- Mathematics: closed for node 1's zero-content root responsibility.
- Work: exact zero count and polynomial bound are implemented.
- Trust: current direct checks report only `propext`, `Classical.choice`, and
  `Quot.sound`.
- Evidence: reviewed matrix row points to
  `generated/hypostructure/web/snapshot.json`; web generation and widening
  audits remain ordinary packet gates.

Node 2 is the next topology-ready implementation packet, but Node 1 is not
`migrated_closed` until the clean semantic parity baseline exists.
