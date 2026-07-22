# EG Node 9 Migration Packet

Date: 2026-07-22

Status: focused Graph deletion criticality checked; semantic parity baseline
pending

## Authority Snapshot

The sole mathematical and DAG authority is
`original_erdos_64_proof.tex`, pinned by
`migration/hypostructure/source-authority.json` at SHA-256
`215248521b7dbc6519076d506101b80a1c9a8425ee5c13b48a4ec52df21d2e10`.
The living proof is not an obligation source.

The frozen original statements are:

- diagram node `[9]`: `edge deletion critical; every edge touches a
  degree-$3$ vertex` (original line 579);
- direct incoming edge: `[8] -> [9]` (original line 603);
- direct outgoing edge: `[9] -> [10]` (original line 604);
- table item `[9], [10]`: high-degree independence, with the failure route
  high-high edge deletion, citing `\cref{lem:deletion-critical}` (original
  line 1095);
- task list item `[9]`: `Every edge touches a degree-$3$ vertex`, citing
  `\cref{lem:deletion-critical}` (original line 1181);
- `\cref{lem:deletion-critical}`: every edge of `G` has at least one endpoint
  of degree `3`; in particular high-degree vertices are independent.  The
  proof deletes a high-high edge, preserves the minimum-degree baseline and
  target avoidance, and contradicts minimality/no-proper-core (original lines
  1788-1795).

Node 9 owns only the pointwise degree-three endpoint assertion.  Node 10 owns
the high-degree independence corollary.

## Mandatory Contract

| Field | Frozen value |
|---|---|
| Node ID | 9 |
| Literal predecessor | `Node8Stage` |
| Incoming branch | Node 8 active residual, `[8] -> [9]` |
| Incoming queries | `node4ContextAtNode8Query`, `node8CertificateQuery` |
| Inherited facts | Minimal counterexample context and no-proper-core certificate |
| Local responsibility | Every edge has a degree-three endpoint |
| New payload | `Graph.DeletionCriticalityCertificate` |
| Executor | `Graph.executeFocusedMinimumDegreeDeletionCriticalityCounted` |
| Closure mechanism | `Core.Closure.Mechanism.strictProgress`, inherited through node 8's no-proper-core contradiction |
| Complementary residuals | None inside node 9; non-tight high-high edges contradict the inherited no-proper-core certificate |
| Outgoing consumers | Node 10 consumes the endpoint certificate to prove high-degree independence |

The legal state flow is:

```text
Node8Stage
  -> Node8Focus active branch
  -> node4ContextAtNode8Query reads the retained minimal context
  -> node8CertificateQuery reads the no-proper-core certificate
  -> Graph.executeFocusedMinimumDegreeDeletionCriticalityCounted
  -> Graph.DeletionCriticalityCertificate
  -> Node9Stage
```

## Provision Boundary

| Input | Role | Reason |
|---|---|---|
| `node9MinimumDegreeThreshold` | semantic law | Instantiates the paper's fixed minimum-degree threshold `3` |
| `node4ContextAtNode8Query` | predecessor projection | Retrieves the minimal context from the literal node-8 residual |
| `node8CertificateQuery` | predecessor projection | Retrieves node 8's framework-owned no-proper-core certificate |

Framework-generated values are kept separate:

- `Graph.deriveDeletionCriticality` owns the high-slack edge deletion
  contradiction;
- `Graph.executeFocusedMinimumDegreeDeletionCriticalityCounted` owns focused
  execution and work accounting;
- `node9CertificateQuery` retrieves the generated endpoint certificate; and
- `node9Metadata` records no manual obligations.

## Legacy Difference

The legacy node 9 exposed the same paper-visible endpoint predicate as a
dependent successor output.  The Hypostructure-native node keeps the output as
Graph's generic deletion-criticality certificate on the accumulated focused
stage; the parity module compares only the normalized endpoint statement.

## Completion Gates

| Gate | Evidence |
|---|---|
| Kernel | `lake env lean HypostructureErdos64EG/Node9.lean` and `lake build HypostructureErdos64EG.Node9` |
| Parity | `examples/hypostructure_parity/HypostructureParity/Erdos64EG/Node9.lean` checks; clean semantic baseline remains pending |
| Mathematics | Closed: `node9_edge_touches_degree_three` proves the exact local responsibility from `lem:deletion-critical` |
| Work | Captured by `node9Counted_work_bounded` and `node9_metadata_work_bounded` |
| Trust | `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound` |
| Web | `generated/hypostructure/web/snapshot.json` after `make web-data` |

Node 10 is the next dependency-ready packet.
