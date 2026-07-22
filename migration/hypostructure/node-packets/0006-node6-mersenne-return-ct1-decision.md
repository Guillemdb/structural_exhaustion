# EG Node 6 Migration Packet

Date: 2026-07-22

Status: focused Graph CT1 decision checked; semantic parity baseline pending

## Authority Snapshot

The sole mathematical and DAG authority is
`original_erdos_64_proof.tex`, pinned by
`migration/hypostructure/source-authority.json` at SHA-256
`215248521b7dbc6519076d506101b80a1c9a8425ee5c13b48a4ec52df21d2e10`.
The living proof is not an obligation source.

The frozen original statements are:

- diagram node `[6]`: `Mersenne return exists?` (original line 576);
- direct incoming edge: `[5] -> [6]` (original line 600);
- yes outgoing edge: `[6] -- yes -> [7]` (original line 601);
- no outgoing edge: `[6] -- no -> [8]` (original line 602);
- table item `[5]--[7]`: edge-rooted target equivalence, no `C_{2^j}`
  iff all `R_e(G)\cap\Mers=\varnothing`, with a Mersenne return giving a
  target cycle (original line 1093);
- framework branch table: a Mersenne return closes by
  `\cref{lem:return-equivalence}` (original lines 1733-1747).

Node 6 performs only the CT1 decision over the selected graph's edge-rooted
Mersenne-return certificate space and the framework-owned continuation from
the impossible C1 arm to the avoiding residual. Node 7 owns the terminal
power-of-two-cycle closure, and Node 8 owns the no-return residual.

## Mandatory Contract

| Field | Frozen value |
|---|---|
| Node ID | 6 |
| Literal predecessor | `Node5Stage` |
| Incoming branch | Node 5 focused target-algebra branch |
| Incoming queries | `node4ContextAtNode5Query`, `node5CertificateQuery` |
| Inherited facts | Selected graph and rooted-return avoidance certificate |
| Local responsibility | CT1 decision: Mersenne return exists? |
| New payload | `CT1.FocusedCertificateEncoding.Route` and terminal-indexed evidence |
| Executor | `Graph.CT1.executeFocusedRootedReturnCounted` |
| C1 continuation | `node6Encoding.closeC1ContinueAvoidingCounted` |
| Complementary residuals | C1 terminal consumed by Node 7; avoiding residual consumed by Node 8 |
| Outgoing consumers | Node 7 and Node 8 |

The legal state flow is:

```text
Node5Stage
  -> Node5Focus active branch
  -> node6ObjectQuery
  -> Graph.CT1.focusedRootedReturnEncoding
  -> Graph.CT1.executeFocusedRootedReturnCounted
  -> CT1 terminal route
  -> node6Encoding.closeC1ContinueAvoidingCounted using node6TargetImpossibleQuery
  -> Node6AvoidingStage
```

## Provision Boundary

| Input | Role | Reason |
|---|---|---|
| `node6Encoding` | semantic law | Instantiates the generic focused rooted-return CT1 encoding |
| `node6ObjectQuery` | predecessor projection | Reads the selected graph from the Node 5 residual |
| `node6TargetImpossibleQuery` | semantic law | Converts the inherited Node 5 avoidance certificate into target impossibility |

Framework-generated values are kept separate:

- `Graph.CT1.executeFocusedRootedReturnCounted` owns CT1 execution;
- `node6RouteQuery` retrieves the generated terminal route;
- `node6_semantics` exposes terminal-indexed target semantics;
- `node6_trace_exact` exposes CT1's exact public trace;
- `node6ContinueAvoidingCounted` owns the impossible-C1 continuation; and
- `node6Metadata` plus `node6ContinueAvoidingMetadata` record no manual
  obligations.

## Legacy Difference

The legacy `Erdos64EG.Node6` file uses a residual-refinement CT1 dependent
certificate family and exposes `node6_semantics`, `node6_trace_exact`,
`node6_work_bound`, and `node6_total`.

Hypostructure normalizes this to the public focused certificate CT1 route:

- terminal `.c1` means the public target holds;
- terminal `.avoiding` means the public target is avoided;
- the trace is read through `CT1.CertificateEncoding.traceOfRoute`; and
- work is bounded by the focused encoding's polynomial budget.

The legacy continuation to the no-return branch is named downstream through
Node 7 machinery. Hypostructure exposes the same paper residual directly as
`Node6AvoidingStage`, because the inherited Node 5 certificate rules out the
C1 branch and the framework continuation produces the avoiding residual for
Node 8.

## Local Obligations

| Task | Declaration | Expected result |
|---|---|---|
| Graph read | `node6ObjectQuery` | Retrieves the selected graph through a focused query |
| CT1 encoding | `node6Encoding` | Instantiates focused rooted-return CT1 |
| CT1 execution | `node6` | Executes the public focused graph CT1 executor |
| Route query | `node6RouteQuery` | Retrieves CT1 terminal and evidence |
| Semantics | `node6_semantics` | Terminal `.c1` gives target, `.avoiding` gives no target |
| Trace | `node6_trace_exact` | Exact CT1 terminal-indexed trace |
| Work | `node6_work_bound` | Route checks are at most one |
| Counted work | `node6Counted_work_bounded` | Focused CT1 polynomial bound |
| Impossible C1 | `node6TargetImpossibleQuery` | Inherited Node 5 certificate rules out target |
| Avoiding continuation | `node6ContinueAvoiding` | Produces the Node 8 avoiding residual |
| Avoiding evidence | `node6_avoids` | Avoiding residual carries `¬ Target` |
| Avoiding work | `node6_avoiding_work` | Avoiding branch performs zero validation checks |
| Metadata | `node6MetadataComplete` | CT1 execution has no manual obligations |
| Metadata | `node6ContinueAvoidingMetadataComplete` | Continuation has no manual obligations |
| Parity | `HypostructureParity.Erdos64EG.Node6.legacy_counterexample_routes_to_node6` | Legacy-visible counterexample reaches the new Node 6 CT1 route |
| Parity | `HypostructureParity.Erdos64EG.Node6.selected_ct1_semantics` | New CT1 route exposes the same public branch semantics |
| Parity | `HypostructureParity.Erdos64EG.Node6.selected_continue_avoids` | Continuation exposes the no-return residual |

## Completion Gates

- Kernel: direct `HypostructureErdos64EG.Node6` source elaborates and builds.
- Parity: direct normalized parity module kernel-checks, but the reviewed
  semantic parity field remains blocked until a clean baseline manifest is
  frozen.
- Mathematics: closed for Node 6's CT1 decision and no-return continuation
  responsibility.
- Work: CT1 route validation is at most one check; total execution and
  continuation have framework polynomial focus-selection bounds.
- Trust: current direct checks report only `propext`, `Classical.choice`, and
  `Quot.sound`.
- Evidence: reviewed matrix row points to
  `generated/hypostructure/web/snapshot.json`; web generation remains the
  package evidence gate.

Node 7 is the exact C1 terminal consumer. Node 8 is the exact avoiding
residual consumer.
