# EG Node 5 Migration Packet

Date: 2026-07-22

Status: direct rooted-return target algebra checked; semantic parity baseline pending

## Authority Snapshot

The sole mathematical and DAG authority is
`original_erdos_64_proof.tex`, pinned by
`migration/hypostructure/source-authority.json` at SHA-256
`215248521b7dbc6519076d506101b80a1c9a8425ee5c13b48a4ec52df21d2e10`.
The living proof is not an obligation source.

The frozen original statements are:

- diagram node `[5]`: target algebra
  `R_e(G)\cap\Mers=\varnothing` for every oriented edge
  (original line 575);
- direct incoming edge: `[4] -> [5]` (original line 599);
- direct outgoing edge: `[5] -> [6]` (original line 600);
- table item `[5]--[7]`: edge-rooted target equivalence, no `C_{2^j}`
  iff all `R_e(G)\cap\Mers=\varnothing`, with a Mersenne return giving a
  target cycle (original line 1093);
- definition `Mersenne return set` and lemma `Edge-rooted target
  equivalence` (original lines 1640 and 1651).

Node 5 performs only the graph-owned target/return dictionary and avoidance
certificate. It does not decide whether a Mersenne return exists; that is Node
6. It does not close the return branch; that is Node 7.

## Mandatory Contract

| Field | Frozen value |
|---|---|
| Node ID | 5 |
| Literal predecessor | `Node4Stage` |
| Incoming branch | Node 4 focused minimal-counterexample branch |
| Incoming queries | `node4ContextQuery`, preserved as `node4ContextAtNode5Query` |
| Inherited facts | Selected minimal context and target avoidance |
| Local responsibility | Instantiate edge-rooted Mersenne target algebra |
| New payload | `mersenneReturnAlgebra.AvoidanceCertificate ctx.G` |
| Executor | `Core.Residual.Focus.runCounted` plus `Graph.RootedReturnTargetAlgebra.avoidanceCertificate` |
| Complementary residuals | None at Node 5; Node 6 performs the return decision |
| Outgoing consumer | Node 6 |

The legal state flow is:

```text
Node4Stage
  -> Node4Focus active branch
  -> node4ContextQuery.read
  -> Graph.RootedReturnTargetAlgebra.avoidanceCertificate
  -> Core.Residual.Focus.Stage Node4Focus Node5Output
```

## Provision Boundary

| Input | Role | Reason |
|---|---|---|
| `mersenneReturnAlgebra` | semantic law | Instantiates the generic shifted-return profile with the EG Mersenne predicate |
| `node4ContextQuery` | predecessor projection | Reads the selected minimal context from Node 4 |

Framework-generated values are kept separate:

- `Core.Residual.Focus.runCounted` owns the focused successor stage and
  inactive-sibling preservation;
- `Graph.RootedReturnTargetAlgebra.avoidanceCertificate` owns the
  target-avoidance to return-set-disjointness conversion;
- `node5CertificateQuery` retrieves the latest focused payload for Node 6;
- `node4ContextAtNode5Query` preserves the Node 4 context without copying it;
  and
- `node5Metadata` records no manual obligations.

## Legacy Difference

The legacy `Erdos64EG.Node5` file stores a local record
`Node5TargetAlgebra` containing both `targetIffReturn` and
`returnSetsDisjoint`, and records `node5LocalChecks = 0`.

Hypostructure normalizes this to:

- the public Graph theorem
  `RootedReturnTargetAlgebra.target_iff_hasRootedReturn`;
- the framework-owned `AvoidanceCertificate`, queried by
  `node5CertificateQuery`; and
- one counted focused-successor check from `Core.Residual.Focus.runCounted`.

The work-count difference is framework accounting: the graph target algebra
performs no finite search, while the residual executor records one focused
branch continuation.

## Local Obligations

| Task | Declaration | Expected result |
|---|---|---|
| Mersenne profile | `mersenneReturnAlgebra` | EG return predicate is the shifted dyadic target predicate |
| Focused execution | `node5` | Extends only the Node 4 active branch |
| Certificate query | `node5CertificateQuery` | Retrieves the graph-owned avoidance certificate |
| Context preservation | `node4ContextAtNode5Query` | Retrieves the selected Node 4 context through the Node 5 stage |
| Target algebra | `node5_target_iff_rootedReturn` | Exposes target iff rooted Mersenne return |
| Exact work | `node5Counted_checks_eq_one` | One focused-successor check |
| Work bound | `node5Counted_work_bounded` | Core focus-selection polynomial bound |
| Metadata | `node5MetadataComplete` | No manual obligations |
| Parity | `HypostructureParity.Erdos64EG.Node5.legacy_counterexample_routes_to_node5` | Legacy-visible counterexample reaches the new Node 5 focus |
| Parity | `HypostructureParity.Erdos64EG.Node5.selected_target_algebra_facts` | Selected context exposes target/return equivalence |
| Parity | `HypostructureParity.Erdos64EG.Node5.selected_return_sets_disjoint` | Selected context exposes per-dart Mersenne-return disjointness |

## Completion Gates

- Kernel: direct `HypostructureErdos64EG.Node5` source elaborates.
- Parity: direct normalized parity module kernel-checks, but the reviewed
  semantic parity field remains blocked until a clean baseline manifest is
  frozen.
- Mathematics: closed for Node 5's target-algebra responsibility.
- Work: exact one-check focused-successor continuation and polynomial bound
  are implemented; legacy zero-check local algebra is documented as a
  normalized accounting difference.
- Trust: current direct checks report only `propext`, `Classical.choice`, and
  `Quot.sound`.
- Evidence: reviewed matrix row points to
  `generated/hypostructure/web/snapshot.json`; web generation remains the
  package evidence gate.

Node 6 is the exact original downstream consumer on the counterexample path.
