# Structural Exhaustion: numbered mathematical-obligation schemas

This package converts the CT1–CT17 tactic diagrams in `branch_closure_methodology_extended(2).tex` into a numbered, machine-readable proof-obligation graph.

The extraction contains **17 tactics, 314 numbered nodes, and 301 numbered transitions**.

## Core model

A tactic is not merely a diagram and not merely a linear list. It is:

1. an **ordered array of node specifications**, which gives stable source-order identifiers such as `CT1.N01`; and
2. an **explicit transition graph**, which gives the real branching, handoff, recovery, scope, and loop control flow.

Every node is a mathematical obligation. A node records:

- a stable number and ID;
- a node type and proof modality;
- an informal, LaTeX, or formal statement;
- typed inputs and outputs;
- dependencies;
- one or more contract schemas that must be instantiated;
- explicit outgoing transitions;
- a discharge criterion;
- terminal data when it is a certificate, payload handoff, scope candidate, or admission reject.

## Typed field documentation and source provenance

Every JSON instance field declared by a schema has a nonempty `description`. The description states the field's mathematical role and the content needed for a valid proof artifact, including nested branch, payload, certificate, contract, evidence, run, and verification records.

The descriptions distinguish two source layers:

1. `final_curvature_compression_fullproof_professional_flow.tex` supplies the concrete proof-instance mathematics: the minimal bad graph, Mersenne returns, target-complete replacement, the induced-`P13` packing and remainder, positive deficiency, curvature rank, the entropy comparison, negative net charge, and local capacity.
2. `source/branch_closure_methodology_extended_numbered.tex` supplies the package's pre-existing framework vocabulary: CT1–CT17 identifiers, branch-state fields, S-/A-contract names, C1–C5 certificate classes, payload routing, and tactic-run semantics. The final-curvature manuscript does not itself define those identifiers, so the schemas do not invent a one-to-one mapping between CT1–CT17 and its 18 proof-flow steps.

Run the description-coverage check after changing any schema:

```bash
python3 tools/validate_schema_descriptions.py
```

## Node-type obligations

| Node type | Required mathematical role | Main contract |
|---|---|---|
| `input` | Verify the incoming payload or trigger signature | `S-Trig` |
| `definition` | Define a typed object from the recorded branch state | `S-Def` |
| `residual_record` | Define the residual-state record and its fields | `S-Def` |
| `assertion` | Prove the displayed proposition | `S-Prove`, plus specialized contracts |
| `decision` | Prove that the displayed alternatives exhaust the residual class | `S-Dich` |
| `comparison` | Prove a numerical, finite, order, capacity, rank, or arithmetic comparison | `S-Comp` |
| `loop_measure` | Define a well-founded measure and prove strict descent | `S-Meas` |
| `payload_constructor` | Construct a typed payload and name its consumer | `S-Rout` |
| `consumer_handoff` | Verify that the payload satisfies the consumer trigger | `S-Trig` |
| `certificate` | Validate a C1–C5 certificate and its supporting contracts | `A-Cert` |
| `recovery` | Construct a typed repair object rather than leave a prose residual | `S-Def`, `S-Rout` |
| `scope_audit` | Prove non-expressibility in the current proof language, or replace it by a repair | `A-Scope` |
| `audit_gate` | Reject execution before it begins and record the failed admission condition | `A-Admission` |

`S-Prove`, `A-Cert`, `A-Scope`, and `A-Admission` are recommended additions to the manuscript’s current alphabet. They close gaps not covered by the existing interface contracts.

## Four separate artifact types

Do not collapse these into one object:

1. **`tacticSpec`** — the static ordered graph of obligations.
2. **`nodeProofRecord`** — evidence discharging one node obligation.
3. **`tacticVerification`** — a complete proof package containing one successful discharge for every node, in stable node order.
4. **`tacticRun`** — one actual branch through the graph; it contains only visited nodes and may repeat nodes on a declared loop.

This distinction matters: a tactic verification must cover every branch, while a tactic run must not pretend that every branch was executed.

## Contract-instance schemas

The bundle includes field-level schemas for:

- `S-Prove`, `S-Def`, `S-Equiv`, `S-Dich`, `S-Pers`, `S-Det`;
- `S-Rout`, `S-Trig`, `S-Comp`, `S-Rest`, `S-Meas`;
- `A-Cert`, `A-Scope`, `A-Admission`.

A completed node record therefore stores both:

- `dischargedContracts`: the contract names; and
- `contractInstances`: structured evidence objects satisfying those contract schemas.

## Files

### Generic schemas

- `schemas/structural-exhaustion.bundle.schema.json` — self-contained JSON Schema Draft 2020-12 bundle.
- `schemas/node.schema.json` — generic node specification.
- `schemas/tactic.schema.json` — generic tactic specification.
- `schemas/tactic-library.schema.json` — collection of tactics.
- `schemas/contract-instance.schema.json` — union of all mathematical contract schemas.
- `schemas/contracts/*.schema.json` — one reusable schema for each S-* or A-* contract.
- `schemas/node-proof-record.schema.json` — one node’s proof/evidence record.
- `schemas/tactic-verification.schema.json` — complete all-node verification.
- `schemas/tactic-run.schema.json` — one execution path.

### Concrete CT1–CT17 schemas

- `schemas/concrete/tactics/CT1.schema.json` … `CT17.schema.json` — exact ordered node arrays for the present tactics.
- `schemas/concrete/nodes/*.schema.json` — one completed-discharge schema for each of the 314 numbered nodes.
- `schemas/concrete/verifications/*.verification.schema.json` — one complete proof-package schema per tactic.
- `schemas/concrete/runs/*.run.schema.json` — one branch-run schema per tactic.

### Extracted data and source

- `data/ct1-ct17.numbered.json` — every tactic, node, obligation, and transition.
- `data/node-index.csv` — compact index of all 314 nodes.
- `source/branch_closure_methodology_extended_numbered.tex` — all tactic-diagram nodes visibly labelled `CTk.Nnn`.
- `tools/validate_tactics.py` — graph-level semantic linter.
- `MANUAL_REVIEW.md` — what still requires mathematical author review.

## Why JSON Schema is not enough

JSON Schema can validate local object shape, required fields, enums, and contract-instance structure. It cannot generally prove cross-object graph facts such as:

- consecutive numbering;
- reachability from an entry node;
- equality between declared and actual outgoing branches;
- unique payload consumers across a graph;
- path validity for a tactic run;
- well-foundedness of a mathematical measure;
- semantic truth of a lemma.

Run the semantic linter after JSON Schema validation:

```bash
python3 tools/validate_tactics.py data/ct1-ct17.numbered.json
```

## Recommended authoring workflow

1. Make the JSON tactic specification the canonical source of IDs, statements, contracts, dependencies, and routes.
2. Generate TikZ diagrams, tactic ledgers, node indexes, and worksheet shells from that JSON.
3. Fill each node’s typed inputs, outputs, formal statement, and contract instances.
4. Validate local structure with JSON Schema.
5. Validate graph invariants with the semantic linter.
6. Require a complete `tacticVerification` before admitting the tactic to the library.
7. Record each use as a `tacticRun` ending only in a certificate, typed payload, admission reject, or audited scope candidate.

## Numbering rule

Node numbers are stable source-order identifiers, not a claim of total execution order. A branch may skip later-numbered nodes, and a well-founded loop may return to an earlier-numbered node. The transition graph is authoritative for execution.
