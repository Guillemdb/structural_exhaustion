# EG Node 4 Migration Packet

Date: 2026-07-22

Status: direct focused minimal selection checked; semantic parity baseline pending

## Authority Snapshot

The sole mathematical and DAG authority is
`original_erdos_64_proof.tex`, pinned by
`migration/hypostructure/source-authority.json` at SHA-256
`215248521b7dbc6519076d506101b80a1c9a8425ee5c13b48a4ec52df21d2e10`.
The living proof is not an obligation source.

The frozen original statements are:

- diagram node `[4]`: `choose lexicographically minimal counterexample`
  (original line 574);
- direct incoming edge: `[2] -- yes -> [4]` (original line 598);
- direct outgoing edge: `[4] -> [5]` (original line 599);
- table item `[4]`: choose minimal `(|V|, |E|)` counterexample, with
  smaller counterexample impossible (original line 1092);
- minimality prose: choose a counterexample lexicographically minimal by
  `(|V(G)|, |E(G)|)` (original line 1722).

Node 4 performs only the positive-branch minimal-counterexample selection. It
does not introduce edge-rooted target algebra, Mersenne returns, no-proper-core
facts, deletion criticality, or rank identities.

## Mandatory Contract

| Field | Frozen value |
|---|---|
| Node ID | 4 |
| Literal predecessor | `Node2Stage` |
| Incoming branch | Node 2 `yes` branch |
| Incoming queries | `node2CounterexampleQuery` and `node1ResidualAtNode2Query` |
| Inherited facts | Root graph, baseline proof, and target-avoidance proof |
| Local responsibility | Select a lexicographically minimal counterexample |
| New payload | `Core.MinimalCounterexampleContext problem Target EGProgress` |
| Executor | `Core.Residual.Focus.runCounted` plus `Graph.selectLexicographicMinimal` |
| Complementary residuals | Node 2 `no` branch remains consumed by Node 3 |
| Outgoing consumer | Node 5 |

The legal state flow is:

```text
Node2Stage
  -> Core.Residual.Focus.yes active proof
  -> node2CounterexampleQuery.and node1ResidualAtNode2Query
  -> Graph.selectLexicographicMinimal
  -> Core.Residual.Focus.Stage CounterexampleFocus Node4Output
```

## Provision Boundary

| Input | Role | Reason |
|---|---|---|
| `node2CounterexampleQuery` | predecessor projection | Reads the exact Node 2 positive proof |
| `node1ResidualAtNode2Query` | predecessor projection | Reads the unchanged theorem-root graph and baseline |
| `fun _current => ()` | definition | Initializes the problem's unit branch state |

Framework-generated values are kept separate:

- `Core.Residual.Focus.yes` owns branch activity;
- `Core.Residual.Focus.runCounted` owns the focused ledger extension;
- `Graph.selectLexicographicMinimal` owns the well-founded minimal selection;
- `node4ContextQuery` retrieves the latest focused payload for downstream
  nodes; and
- `node4Metadata` records no manual obligations.

## Legacy Difference

The legacy `Erdos64EG.Node4` file selects
`Graph.PackedMinimumDegreeCycle.StaticInput.SelectedMinimalContext` and proves
a rank bound against the original graph through
`runInitialThroughNode4_minimal`. Hypostructure normalizes this to the public
paper-level fact: the selected object is a `Core.MinimalCounterexampleContext`
for `EGProgress`, whose `minimal` kernel closes every strictly smaller
baseline target-avoiding graph.

Parity is therefore stated against:

- the legacy-visible counterexample predicate, transported by Node 2 parity;
- the Hypostructure Node 4 active focus; and
- the selected context's baseline, target avoidance, and minimality kernel.

## Local Obligations

| Task | Declaration | Expected result |
|---|---|---|
| Positive branch read | `node2CounterexampleQuery` | Retrieves the Node 2 counterexample proof |
| Root read | `node1ResidualAtNode2Query` | Retrieves the unchanged Node 1 residual |
| Input product | `node4InputQuery` | Reads both inputs through one active query |
| Focused execution | `node4` | Extends only the positive branch |
| Minimality payload | `node4ContextQuery_minimal` | Exposes the selected Core minimality kernel |
| Exact work | `node4Counted_checks_eq_one` | One focus-selection check |
| Work bound | `node4Counted_work_bounded` | Core focus-selection polynomial bound |
| Metadata | `node4MetadataComplete` | No manual obligations |
| Parity | `HypostructureParity.Erdos64EG.Node4.legacy_counterexample_routes_to_node4` | Legacy-visible counterexample reaches the new Node 4 focus |
| Parity | `HypostructureParity.Erdos64EG.Node4.selected_context_facts` | Selected context exposes baseline, avoidance, and minimality |

## Completion Gates

- Kernel: direct `HypostructureErdos64EG.Node4` build is fresh.
- Parity: direct normalized parity module kernel-checks, but the reviewed
  semantic parity field remains blocked until a clean baseline manifest is
  frozen.
- Mathematics: closed for Node 4's minimal-counterexample selection
  responsibility.
- Work: exact one-check focused-branch selection and polynomial bound are
  implemented.
- Trust: current direct checks report only `propext`, `Classical.choice`, and
  `Quot.sound`.
- Evidence: reviewed matrix row points to
  `generated/hypostructure/web/snapshot.json`; web generation remains the
  package evidence gate.

Node 5 is the exact original downstream consumer on the counterexample path.
