# EG Node 8 Migration Packet

Date: 2026-07-22

Status: focused Graph proper-subgraph minimality checked; semantic parity
baseline pending

## Authority Snapshot

The sole mathematical and DAG authority is
`original_erdos_64_proof.tex`, pinned by
`migration/hypostructure/source-authority.json` at SHA-256
`215248521b7dbc6519076d506101b80a1c9a8425ee5c13b48a4ec52df21d2e10`.
The living proof is not an obligation source.

The frozen original statements are:

- diagram node `[8]`: `no proper subgraph with minimum degree 3`
  (original line 578);
- direct incoming edge: `[6] -- no -> [8]` (original line 602);
- direct outgoing edge: `[8] -> [9]` (original line 603);
- table item `[8]`: every proper subgraph has `δ <= 2`; a proper smaller
  counterexample is the failure route (original line 1094);
- `\cref{lem:no-proper-core}`: every proper subgraph `H ⊊ G` satisfies
  `δ(H) <= 2`, by minimality of `G` (original lines 1780-1787).

Node 8 consumes the no-return avoiding residual produced by node 6. Node 7 is
the sibling C1 terminal and is not part of this residual.

## Mandatory Contract

| Field | Frozen value |
|---|---|
| Node ID | 8 |
| Literal predecessor | `Node6AvoidingStage` |
| Incoming branch | Node 6 avoiding branch, `[6] -- no -> [8]` |
| Incoming queries | `node4ContextAtNode6AvoidingQuery`, `node6AvoidingQuery` |
| Inherited facts | Minimal counterexample context and target avoidance |
| Local responsibility | Exclude every proper subgraph preserving the baseline |
| New payload | `Graph.NoProperBaselineCertificate` |
| Executor | `Graph.executeFocusedNoProperBaselineCounted` |
| Closure mechanism | `Core.Closure.Mechanism.strictProgress` |
| Complementary residuals | None inside node 8; proper-core hypotheses close by strict progress |
| Outgoing consumers | Node 9 consumes the no-proper-core certificate |

The legal state flow is:

```text
Node6AvoidingStage
  -> Node6AvoidingFocus active branch
  -> node4ContextAtNode6AvoidingQuery reads the retained minimal context
  -> node8MinimalityProfile supplies target monotonicity for cycle targets
  -> Graph.executeFocusedNoProperBaselineCounted
  -> Graph.NoProperBaselineCertificate
  -> Node8Stage
```

## Provision Boundary

| Input | Role | Reason |
|---|---|---|
| `node8MinimalityProfile` | semantic law | Instantiates the reusable proper-subgraph minimality profile for the EG cycle target |
| `node4ContextAtNode6AvoidingQuery` | predecessor projection | Retrieves the minimal context from the literal node-6 avoiding residual |

Framework-generated values are kept separate:

- `Graph.deriveNoProperBaseline` owns the strict-progress contradiction;
- `Graph.executeFocusedNoProperBaselineCounted` owns focused execution and
  work accounting;
- `node8CertificateQuery` retrieves the generated certificate; and
- `node8Metadata` records no manual obligations.

## Legacy Difference

The legacy node 8 exposed the same no-proper-core predicate together with an
older CT2 deletion-C2 trace for each hypothetical proper core. The
Hypostructure-native node uses the new Graph-level strict-progress closure
directly; the parity module records the legacy CT2 trace only as test-only
behavioral evidence.

## Completion Gates

| Gate | Evidence |
|---|---|
| Kernel | `lake env lean HypostructureErdos64EG/Node8.lean` and `lake build HypostructureErdos64EG.Node8` |
| Parity | `examples/hypostructure_parity/HypostructureParity/Erdos64EG/Node8.lean` checks; clean semantic baseline remains pending |
| Mathematics | Closed: `node8_noProperCore` proves the exact `lem:no-proper-core` local responsibility |
| Work | Captured by `node8Counted_work_bounded` and `node8_metadata_work_bounded` |
| Trust | `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound` |
| Web | `generated/hypostructure/web/snapshot.json` after `make web-data` |

Node 9 is the next dependency-ready packet.
