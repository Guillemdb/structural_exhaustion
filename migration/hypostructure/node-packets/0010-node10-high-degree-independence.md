# EG Node 10 Migration Packet

Date: 2026-07-22

Status: focused Graph slack-vertex independence checked; semantic parity
baseline pending

## Authority Snapshot

The sole mathematical and DAG authority is
`original_erdos_64_proof.tex`, pinned by
`migration/hypostructure/source-authority.json` at SHA-256
`215248521b7dbc6519076d506101b80a1c9a8425ee5c13b48a4ec52df21d2e10`.
The living proof is not an obligation source.

The frozen original statements are:

- diagram node `[10]`: `$V_{\ge4}(G)$ independent` (original line 580);
- direct incoming edge: `[9] -> [10]` (original line 604);
- direct outgoing edge: `[10] -> [11]` (original line 605);
- table item `[9], [10]`: high-degree independence, with the failure route
  high-high edge deletion, citing `\cref{lem:deletion-critical}` (original
  line 1095);
- invariant item `[10]`: `V_{\ge4}` is independent, the corollary of
  `\cref{lem:deletion-critical}` (original line 1182);
- `\cref{lem:deletion-critical}`: every edge has a degree-three endpoint; in
  particular, the vertices of degree at least four are independent (original
  lines 1788-1795).

Node 10 owns only the high-degree independence corollary.  Node 9 owns the
pointwise degree-three endpoint theorem that makes this corollary immediate.

## Mandatory Contract

| Field | Frozen value |
|---|---|
| Node ID | 10 |
| Literal predecessor | `Node9Stage` |
| Incoming branch | Node 9 active residual, `[9] -> [10]` |
| Incoming queries | `node4ContextAtNode9Query`, `node9CertificateQuery` |
| Inherited facts | Minimal counterexample context and deletion-criticality certificate |
| Local responsibility | Vertices of degree at least four form an independent set |
| New payload | `Graph.SlackVertexIndependence` |
| Executor | `Graph.executeFocusedMinimumDegreeSlackVertexIndependenceCounted` |
| Closure mechanism | None introduced at node 10; the contradiction source is already inside node 9's deletion-criticality certificate |
| Complementary residuals | None inside node 10 |
| Outgoing consumers | Node 11 consumes the high-degree independence residual |

The legal state flow is:

```text
Node9Stage
  -> Node9Focus active branch
  -> node4ContextAtNode9Query reads the retained minimal context
  -> node9CertificateQuery reads the deletion-criticality certificate
  -> Graph.executeFocusedMinimumDegreeSlackVertexIndependenceCounted
  -> Graph.SlackVertexIndependence
  -> Node10Stage
```

## Provision Boundary

| Input | Role | Reason |
|---|---|---|
| `node9MinimumDegreeThreshold` | semantic law | Reuses the paper's fixed minimum-degree threshold `3` from node 9 |
| `node4ContextAtNode9Query` | predecessor projection | Retrieves the minimal context from the literal node-9 residual |
| `node9CertificateQuery` | predecessor projection | Retrieves node 9's framework-owned deletion-criticality certificate |

Framework-generated values are kept separate:

- `Graph.deriveSlackVertexIndependence` owns the independence consequence of
  endpoint criticality;
- `Graph.executeFocusedMinimumDegreeSlackVertexIndependenceCounted` owns
  focused execution and work accounting;
- `node10IndependenceQuery` retrieves the generated independence fact; and
- `node10Metadata` records no manual obligations.

## Legacy Difference

The legacy node 10 exposed the high-degree independence predicate as a
dependent successor output.  The Hypostructure-native node keeps the payload
as Graph's generic slack-vertex independence fact on the accumulated focused
stage; the parity module compares only the normalized independence statement.

## Completion Gates

| Gate | Evidence |
|---|---|
| Kernel | `lake env lean HypostructureErdos64EG/Node10.lean` and `lake build HypostructureErdos64EG.Node10` |
| Parity | `examples/hypostructure_parity/HypostructureParity/Erdos64EG/Node10.lean` checks; clean semantic baseline remains pending |
| Mathematics | Closed: `node10_high_degree_vertices_independent` proves the exact local responsibility from `lem:deletion-critical` |
| Work | Captured by `node10Counted_work_bounded` and `node10_metadata_work_bounded` |
| Trust | `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound` |
| Web | `generated/hypostructure/web/snapshot.json` after `make web-data` |

Node 11 is the next dependency-ready packet.
