# EG Node 3 Migration Packet

Date: 2026-07-22

Status: direct terminal closure checked; semantic parity baseline pending

## Authority Snapshot

The sole mathematical and DAG authority is
`original_erdos_64_proof.tex`, pinned by
`migration/hypostructure/source-authority.json` at SHA-256
`215248521b7dbc6519076d506101b80a1c9a8425ee5c13b48a4ec52df21d2e10`.
The living proof is not an obligation source.

The frozen original statements are:

- diagram node `[2]`: `counterexample? delta(G) >= 3 and no C_{2^j}`
  (original lines 571-573);
- diagram node `[3]`: `not a counterexample` (original lines 573-574);
- direct incoming edge: `[2] -- no -> [3]` (original line 597);
- sibling outgoing edge: `[2] -- yes -> [4]` (original line 598);
- nodes `[1]` through `[3]` jointly implement counterexample setup
  (original detailed-table line 1091).

Node 3 performs only the terminal conversion on Node 2's negative branch. It
does not choose a minimal counterexample, introduce target algebra, or advance
the positive counterexample residual.

## Mandatory Contract

| Field | Frozen value |
|---|---|
| Node ID | 3 |
| Literal predecessor | `Node2Stage` |
| Incoming branch | Node 2 `no` branch |
| Incoming query | `node3TargetQuery` over `Core.Residual.Focus.no` |
| Inherited facts | Node 2 negative-branch proof of `IsNotCounterexample` |
| Local responsibility | Convert target realization into the official theorem conclusion |
| New payload | One Core direct terminal closure |
| Executor | `Core.Closure.Result.direct` |
| Complementary residuals | Node 2 positive branch remains consumed by Node 4 |
| Closure mechanism | `Core.Closure.Mechanism.direct` |

The legal state flow is:

```text
Node2Stage
  -> Core.Residual.Focus.no active proof
  -> node3TargetQuery
  -> target_iff_official_conclusion
  -> Core.Closure.Result.direct
```

## Provision Boundary

| Input | Role | Reason |
|---|---|---|
| `node3TargetQuery` | predecessor projection | Reads the exact Node 2 negative branch proof |
| `node3_officialConclusion` | semantic law | Converts target realization to the official conclusion |
| `target_iff_official_conclusion` | domain theorem | Problem-level equivalence already registered before Node 3 |

Framework-generated values are kept separate:

- `Core.Residual.Focus.no` owns branch activity;
- `Core.Residual.Focus.noProof` owns retrieval of the selected proof;
- `Core.Closure.Result.direct` owns terminal closure; and
- `node3Metadata` records zero manual obligations and the direct closure
  mechanism.

## Legacy Difference

The legacy public `Erdos64EG.Node3` file is only a facade importing Node 2. The
checked legacy terminal content is in `Erdos64EG.InternalProblem`, notably
`target_of_notCounterexample`, `officialConclusion_of_notCounterexample`, and
`runInitialCounterexampleDecision_exhaustive`.

Parity is normalized to the public terminal proposition:

- legacy `Target` on the normalized graph;
- Hypostructure `Node3OfficialConclusion` for the same root graph; and
- the new direct closure proof on the Node 2 negative branch.

## Local Obligations

| Task | Declaration | Expected result |
|---|---|---|
| Branch read | `node3TargetQuery` | Retrieves the Node 2 negative proof |
| Official conclusion | `node3_officialConclusion` | Produces the theorem conclusion for the unchanged root graph |
| Closure | `node3` | Direct Core closure of the terminal branch |
| Closure tag | `node3_closure_mechanism` | Mechanism is exactly `direct` |
| Exact work | `node3_checks_eq_zero` | Proof-only terminal performs zero primitive checks |
| Work bound | `node3_work_bounded` | Core proof-only polynomial bound |
| Metadata | `node3MetadataComplete` | No manual obligations |
| Parity | `HypostructureParity.Erdos64EG.Node3.officialConclusion_iff_legacy_target` | Same terminal proposition |
| Parity | `HypostructureParity.Erdos64EG.Node3.node3_closure_proves_legacy_target` | New closure implies legacy-visible terminal |

## Completion Gates

- Kernel: direct `HypostructureErdos64EG.Node3` build is fresh.
- Parity: direct normalized parity module kernel-checks, but the reviewed
  semantic parity field remains blocked until a clean baseline manifest is
  frozen.
- Mathematics: closed for Node 3's negative-branch terminal responsibility.
- Work: exact zero-check proof-only budget is implemented.
- Trust: current direct checks report only `propext`, `Classical.choice`, and
  `Quot.sound`.
- Evidence: reviewed matrix row points to
  `generated/hypostructure/web/snapshot.json`; web generation remains the
  package evidence gate.

Node 4 is the exact original positive-branch consumer when continuing along the
counterexample path.
