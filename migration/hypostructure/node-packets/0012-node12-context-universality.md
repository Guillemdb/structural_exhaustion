# EG Node 12 Migration Packet

Date: 2026-07-22

Status: focused Core proof-projection checked; semantic parity baseline pending

## Authority Snapshot

The sole mathematical and DAG authority is
`original_erdos_64_proof.tex`, pinned by
`migration/hypostructure/source-authority.json` at SHA-256
`215248521b7dbc6519076d506101b80a1c9a8425ee5c13b48a4ec52df21d2e10`.
The living proof is not an obligation source.

The frozen original statements are:

- diagram node `[12]`: context-universality for target-complete
  identifications (original line 582);
- direct incoming edge: `[11] -> [12]` (original line 605);
- direct outgoing edge: `[12] -> [13]` (original line 606);
- table item `[12], [36]`: context universality, with non-universal
  identifications routed as quotient defects, citing
  `\cref{lem:context-universality}` (original line 1098);
- `\cref{lem:context-universality}` states that any two coordinates
  identified in a target-complete quotient have the same target response
  against every `T`-boundaried context, and that a quotient valid only for the
  actual outside context is target-defective (original lines 5592-5602).

Node 12 owns only the definitional projection from a certified
target-complete quotient to all-context response equivalence.  Node 13 owns
the replacement lemma that uses this universality.

## Mandatory Contract

| Field | Frozen value |
|---|---|
| Node ID | 12 |
| Literal predecessor | `Node11Stage` |
| Incoming branch | Node 11 active residual, `[11] -> [12]` |
| Incoming queries | `node11RegistrationQuery` |
| Inherited facts | Node 11 boundaried-atom registration and boundary-degree profile family |
| Local responsibility | Project target-complete identifications to context-universal target-response equivalence |
| New payload | `Core.Residual.ProofProjection.Certificate Node12Claim` |
| Executor | `Core.Residual.ProofProjection.executeCounted` |
| Closure mechanism | None introduced at node 12 |
| Complementary residuals | None inside node 12 |
| Outgoing consumers | Node 13 consumes the context-universality residual |

The legal state flow is:

```text
Node11Stage
  -> Node11Focus active branch
  -> node11RegistrationQuery reads the Graph-generated atom registration
  -> node12ProjectionQuery derives the local implication
  -> Core.Residual.ProofProjection.executeCounted
  -> Core.Residual.ProofProjection.Certificate Node12Claim
  -> Node12Stage
```

## Provision Boundary

| Input | Role | Reason |
|---|---|---|
| `node11RegistrationQuery` | predecessor projection | Retrieves Node 11's framework-owned atom registration from the literal predecessor |
| `node12ProjectionQuery` | registered profile | Core stores exactly the projected proposition on the active branch |

Framework-generated values are kept separate:

- `Graph.AtomResponse.TargetCompleteQuotient.contextUniversal_of_identified`
  owns the context-universality projection;
- `Graph.AtomResponse.CoordinateSystem.in_registered_fibre` owns the
  registered boundary-degree fibre law;
- `Core.Residual.ProofProjection.executeCounted` owns focused execution,
  ledger extension, and work accounting; and
- `node12Metadata` records no manual obligations.

## Legacy Difference

The legacy node 12 exposed a bespoke proposition over pairs of legacy
boundaried atoms.  The Hypostructure-native node keeps the payload as Core's
generic proof-projection certificate over Graph's arbitrary local response
coordinate systems.  The parity module compares the normalized
context-universality implication and the legacy output proposition, not the
private record shapes.

## Completion Gates

| Gate | Evidence |
|---|---|
| Kernel | `lake env lean HypostructureErdos64EG/Node12.lean` and `lake build HypostructureErdos64EG.Node12` |
| Parity | `examples/hypostructure_parity/HypostructureParity/Erdos64EG/Node12.lean` checks; clean semantic baseline remains pending |
| Mathematics | Closed: `node12_context_universal` proves the exact local responsibility from a certified target-complete quotient |
| Work | Captured by `node12Counted_work_bounded`, `node12_work_bounded`, and `node12_metadata_work_bounded` |
| Trust | `#print axioms` reports only the current framework allowlist axioms |
| Web | `generated/hypostructure/web/snapshot.json` after `make web-data` |

Node 13 is the next dependency-ready packet.
