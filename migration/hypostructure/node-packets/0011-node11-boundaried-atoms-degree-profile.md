# EG Node 11 Migration Packet

Date: 2026-07-22

Status: focused Graph boundaried-atom registration checked; semantic parity
baseline pending

## Authority Snapshot

The sole mathematical and DAG authority is
`original_erdos_64_proof.tex`, pinned by
`migration/hypostructure/source-authority.json` at SHA-256
`215248521b7dbc6519076d506101b80a1c9a8425ee5c13b48a4ec52df21d2e10`.
The living proof is not an obligation source.

The frozen original statements are:

- diagram node `[11]`: boundaried atoms and boundary degree profile
  `\mathbf d_\partial` (original line 581);
- direct incoming edge: `[10] -> [11]` (original line 604);
- direct outgoing edge: `[11] -> [12]` (original line 605);
- table item `[11]`: atoms are `T`-boundaried supports under the replacement
  formalism, citing `\cref{def:boundaried-gluing}` (original line 1096);
- table item `[11], [36], [37]`: boundary degree profiles require quotients
  fibrewise over `\mathbf d_\partial`; otherwise target-defective, citing
  `\cref{lem:degree-profile-fibres}` (original line 1097);
- `\cref{def:boundaried-gluing}` and `\cref{def:atom}` define the
  boundaried piece, gluing, atom, context, and proper atom (original lines
  5308-5319);
- `\cref{def:boundary-degree-profile}` defines
  `\mathbf d_\partial(X)=(d_X(v_t))_{t\in T}` and requires
  target-response states to be fibrewise over this profile (original lines
  5320-5327);
- `\cref{lem:degree-profile-fibres}` proves unequal boundary-degree profiles
  cannot be quotient-merged by a target-complete quotient (original lines
  5574-5590).

Node 11 owns only registration of the proper boundaried-atom profile family
and the profile-fibre rejection rule.  Downstream quotient construction and
class enumeration remain node-12 and later responsibilities.

## Mandatory Contract

| Field | Frozen value |
|---|---|
| Node ID | 11 |
| Literal predecessor | `Node10Stage` |
| Incoming branch | Node 10 active residual, `[10] -> [11]` |
| Incoming queries | `node4ContextAtNode10Query` |
| Inherited facts | Minimal counterexample context retained through the node-10 focus |
| Local responsibility | Register proper boundaried atoms with uncapped boundary-degree profiles and reject unequal profile fibres |
| New payload | `Graph.BoundariedAtomRegistration` |
| Executor | `Graph.executeFocusedBoundariedAtomRegistrationCounted` |
| Closure mechanism | None introduced at node 11 |
| Complementary residuals | None inside node 11 |
| Outgoing consumers | Node 12 consumes the boundaried-atom profile residual |

The legal state flow is:

```text
Node10Stage
  -> Node10Focus active branch
  -> node4ContextAtNode10Query reads the retained minimal context
  -> Graph.executeFocusedBoundariedAtomRegistrationCounted
  -> Graph.BoundariedAtomRegistration
  -> Node11Stage
```

## Provision Boundary

| Input | Role | Reason |
|---|---|---|
| `node4ContextAtNode10Query` | predecessor projection | Retrieves the minimal context from the literal node-10 residual |
| `Node10Focus` | predecessor focus | Preserves the active proof branch selected by the framework |

Framework-generated values are kept separate:

- `Graph.deriveBoundariedAtomProfile` owns the uncapped coordinate profile
  for a proper atom;
- `Graph.deriveBoundariedAtomFamily` owns the dependent family over all
  supplied proper atoms;
- `Graph.deriveBoundariedAtomRegistration` owns the profile-fibre rejection
  rule through `Graph.Response.profile_ne_not_targetComplete`;
- `Graph.executeFocusedBoundariedAtomRegistrationCounted` owns focused
  execution and work accounting; and
- `node11Metadata` records no manual obligations.

## Legacy Difference

The legacy node 11 exposed a bespoke `Node11Output` record containing the
boundaried-atom family.  The Hypostructure-native node keeps that payload as
Graph's generic `BoundariedAtomRegistration` on the accumulated focused stage;
the parity module compares only the normalized boundary-degree-profile and
legacy output statements.

## Completion Gates

| Gate | Evidence |
|---|---|
| Kernel | `lake env lean HypostructureErdos64EG/Node11.lean` and `lake build HypostructureErdos64EG.Node11` |
| Parity | `examples/hypostructure_parity/HypostructureParity/Erdos64EG/Node11.lean` checks; clean semantic baseline remains pending |
| Mathematics | Closed: `node11_boundaryDegreeProfile` and `node11_profileMismatchRejected` prove the exact local responsibility |
| Work | Captured by `node11Counted_work_bounded`, `node11_work_bounded`, and `node11_metadata_work_bounded` |
| Trust | `#print axioms` reports only the current framework allowlist axioms |
| Web | `generated/hypostructure/web/snapshot.json` after `make web-data` |

Node 12 is the next dependency-ready packet.
