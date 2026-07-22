# EG Node 2 Migration Packet

Date: 2026-07-22

Status: direct implementation checked; semantic parity baseline pending

## Authority Snapshot

The sole mathematical and DAG authority is
`original_erdos_64_proof.tex`, pinned by
`migration/hypostructure/source-authority.json` at SHA-256
`215248521b7dbc6519076d506101b80a1c9a8425ee5c13b48a4ec52df21d2e10`.
The living proof is not an obligation source.

The frozen original statements are:

- diagram node `[2]`: `counterexample? delta(G) >= 3 and no C_{2^j}`
  (original lines 571-573);
- direct incoming edge: unconditional `[1] -> [2]` (original line 596);
- direct outgoing edge `[2] -- no -> [3]` (original line 597);
- direct outgoing edge `[2] -- yes -> [4]` (original line 598);
- nodes `[1]` through `[3]` jointly implement counterexample setup
  (original detailed-table line 1091).

Node 2 performs only the exhaustive theorem-root counterexample decision. It
does not choose a minimal counterexample, install Mersenne return algebra,
prove replacement facts, or advance any later residual.

## Mandatory Contract

| Field | Frozen value |
|---|---|
| Node ID | 2 |
| Literal predecessor | `Node1Stage` |
| Incoming query | `node1ResidualQuery` |
| Inherited facts | Root object and theorem-supplied minimum-degree baseline |
| Local responsibility | Decide `Baseline object and not Target object` versus `Target object` |
| New payload | One Core-owned binary decision stage |
| Executor | `Core.Residual.Decision.Node.run` through `node2Counted` |
| Outgoing consumers | Node 3 on the no branch; Node 4 on the yes branch |
| Complementary residuals | Both branches retained by `Core.Residual.Decision.Stage` |
| Closure mechanism | None; Node 2 is a routing decision, not a terminal |

The legal state flow is:

```text
Node1Stage
  -> node1ResidualQuery
  -> Core.Residual.Decision.Node.run
  -> Node2Stage
  -> Node3 or Node4
```

## Provision Boundary

| Input | Role | Reason |
|---|---|---|
| `node2Decision.yesDecidable` | decision procedure | The branch proposition is a local logical test |
| `node2Decision.no_of_not_yes` | semantic law | Root baseline converts not-yes into target realization |
| `node1ResidualQuery` | predecessor projection | Reads the literal Node 1 root residual |

Framework-generated values are kept separate:

- `Decision.Binary` owns the selected branch constructor;
- `Ledger.extend` owns the accumulated decision stage;
- `Counted` records exactly one branch inspection; and
- `node2Metadata` records no manual obligation.

## Legacy Difference

The legacy public `Erdos64EG.Node2` facade imports the initial problem setup
but has no standalone theorem body. The actual old executable counterexample
decision lives in `Erdos64EG.Internal.runInitialCounterexampleDecision`, whose
root residual also carries `largeEnoughTail`. That later asymptotic premise is
not part of the original Node 2 contract and is not copied into
Hypostructure.

Parity is therefore normalized to the paper-visible predicates:

- baseline equivalence from Node 1 parity;
- target equivalence through the official-conclusion characterization;
- positive branch equivalence: baseline plus target avoidance; and
- negative branch equivalence: target realization.

## Local Obligations

| Task | Declaration | Expected result |
|---|---|---|
| Binary decision | `node2` | Exact Core decision on the Node 1 predecessor |
| Exhaustiveness | `node2_exhaustive` | The selected constructor proves exactly one paper branch |
| Negative branch forcing | `node2_no_branch_of_target` | A target certificate selects the no branch |
| Positive branch forcing | `node2_yes_branch_of_counterexample` | A counterexample certificate selects the yes branch |
| Exact work | `node2Counted_checks_eq_one` | One primitive branch inspection |
| Budget agreement | `node2Counted_checks_eq_budget` | Count equals registered budget |
| Work bound | `node2_work_bounded` | Core polynomial bound |
| Metadata | `node2MetadataComplete` | No manual obligations |
| Parity | `HypostructureParity.Erdos64EG.Node2.counterexample_iff` | Same positive branch predicate |
| Parity | `HypostructureParity.Erdos64EG.Node2.node2_exhaustive_normalized` | Same branch semantics |

## Completion Gates

- Kernel: direct `HypostructureErdos64EG.Node2` build is fresh.
- Parity: direct normalized parity module kernel-checks, but the reviewed
  semantic parity field remains blocked until a clean baseline manifest is
  frozen.
- Mathematics: closed for Node 2's binary counterexample-decision
  responsibility.
- Work: exact one-check count and polynomial bound are implemented.
- Trust: current direct checks report only `propext`, `Classical.choice`, and
  `Quot.sound`.
- Evidence: reviewed matrix row points to
  `generated/hypostructure/web/snapshot.json`; web generation and widening
  audits remain ordinary packet gates.

Node 3 and Node 4 are the exact original outgoing consumers. Node 3 is already
the no-branch terminal; Node 4 is the next yes-branch packet when continuing
along the counterexample path.
