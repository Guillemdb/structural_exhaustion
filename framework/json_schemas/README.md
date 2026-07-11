# Structural Exhaustion: mathematical-obligation and runtime schemas

This package converts the CT1–CT17 tactic diagrams in `branch_closure_methodology_extended.tex` into machine-readable proof graphs. All 17 tactics use stable semantic runtime-state IDs synchronized with the Lean implementation.

The extraction contains **17 tactics, 206 semantic nodes, and 191 evidence-carrying transitions**. Its node and transition arrays are generated from the formal reference, while the numbered manuscript mirror is synchronized from the same machine definitions.

## Core model

A tactic is not merely a diagram and not merely a linear list. It is:

1. an **ordered array of node specifications**, which gives stable identifiers such as `CT1.certify.equivalence`, `CT2.decide.context`, or `CT4.certify.assignment`; and
2. an **explicit transition graph**, which gives the real branching, handoff, recovery, scope, and loop control flow.

Every node is a mathematical obligation or semantic runtime state. A node records:

- a one-based presentation number and a stable ID;
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

All descriptions are grounded in a single source: the structural exhaustion framework document (`branch_closure_methodology_extended.tex`, mirrored with graph IDs as `source/branch_closure_methodology_extended_numbered.tex`). The schemas exist to type and operationalize that document's components:

- the CT1–CT17 closure-tactic library and its tactic diagrams;
- branch states `B = (H_0, progress record, E, I, R, V, Q, A)` and residual classes;
- the proof language `L = (Sorts, Constructors, Predicates, Measures, Certificates, Payloads, BlackBoxes)`;
- the lemma-schema alphabet S-Def, S-Equiv, S-Dich, S-Pers, S-Det, S-Rout, S-Trig, S-Comp, S-Rest, S-Meas;
- the certificate alphabet C1–C5 and the leaf-totality rule;
- typed payload signatures `P_{i->j}`, ledgers, budgets, and currencies;
- the strategy manual's runtime model, admission gates, defect register, and repair protocol.

`S-Prove`, `A-Cert`, `A-Scope`, and `A-Admission` are package extensions of the framework's lemma-schema alphabet; they operationalize the framework's displayed propositions, certificate validation, scope audit, and admission gates respectively.

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

`S-Prove`, `A-Cert`, `A-Scope`, and `A-Admission` are recommended additions to the framework's current lemma-schema alphabet. They close gaps not covered by the existing interface contracts.

## Four separate artifact types

Do not collapse these into one object:

1. **`tacticSpec`** — the static ordered graph of obligations.
2. **`nodeProofRecord`** — evidence discharging one node obligation.
3. **`tacticVerification`** — a complete proof package containing one successful discharge for every node, in stable node order.
4. **`tacticRun`** — one actual branch through the graph; it contains only visited nodes and may repeat nodes on a declared loop.

This distinction matters: a tactic verification must cover every branch, while a tactic run must not pretend that every branch was executed.

## CT1-v1 semantic runtime graph

CT1 is an exact sequential machine:

`entry → scope → equivalence certification → realization → payload classification`

Scope failure and C1 are exact terminals. A negative realization constructs one `AvoidingState`, and the payload decision routes that state to CT2, CT3, CT4, CT5, CT6, or CT17. Static target-test definitions belong to the framework rather than the runtime graph. Failed equivalence certification is repaired before admission; it is not represented by an execution loop.

The CT2 payload is definitionally aligned with its consumer: its adapter fixes the ambient object and reuses the CT1 target-avoidance proof. As with CT2, `run_total` is relative to supplied proof-producing plans and a handoff plan.

## CT2-v2 semantic runtime graph

CT2 is an exact sequential machine:

`entry → interface → deletion → replacement candidate → context certification`

Exhaustive candidate absence branches from replacement-candidate search to the survivor classifier. The six exact terminals are scope, deletion C2, replacement C2, CT3 context residual, CT10 survivor criticality, and CT3 survivor response defect. The context certificate is specific to the selected candidate. The CT10 payload retains the survivor state and criticality datum; the two CT3 payload variants retain distinct provenance.

`run_total` means totality relative to the supplied proof-producing node plans, `Port`, and `HandoffPlan`. It is not a theorem that witnesses can be found automatically. Likewise, `tacticVerification` records structural all-node and all-branch coverage; it does not assert search completeness.

## CT3-v1 through CT17-v1 semantic runtime graphs

CT3 separates external-type equivalence certification, compression,
defect routing, and finite-table classification. Its seven exact terminals are
scope, C2, C3, C5, CT7, CT12, and CT8.

CT4 separates canonical-assignment certification, payer availability,
bounded-fibre comparison, and the final capacity comparison. Its five exact
terminals are scope, CT13, CT9, C4, and CT14.

CT5 separates locality certification, additive-deficit classification,
summation certification, and global comparison. Its five exact terminals are
scope, CT11, C4, CT4, and CT14. The CT4 payload adapter preserves the ambient
object and branch state definitionally.

CT6 through CT11 and CT13 through CT17 use the same exact-machine discipline:
each proof obligation is an independently typed node, every branch is an
evidence-carrying transition, and every handoff constructs the exact consumer
input. CT11 is deliberately route-only.

CT12 is the unique cyclic graph. Its loop is
`saturation → peel → restoration → decrease → saturation`; only the final
transition may return to saturation, and it carries the strict natural-valued
load decrease required by the Lean executor's well-founded recursion.

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
- `schemas/concrete/nodes/*.schema.json` — one completed-discharge schema for each of the 206 nodes.
- `schemas/concrete/verifications/*.verification.schema.json` — one complete proof-package schema per tactic.
- `schemas/concrete/runs/*.run.schema.json` — one branch-run schema per tactic.

### Extracted data and source

- `data/ct1-ct17.numbered.json` — every tactic, node, obligation, and transition.
- `data/node-index.csv` — compact index of all 206 nodes.
- `source/branch_closure_methodology_extended_numbered.tex` — tactic-diagram nodes labelled by their stable semantic graph IDs.
- `tools/validate_tactics.py` — graph-level semantic linter.
- `tools/sync_ct1_semantic.py` — derives the catalog's CT1-v1 graph and concrete schemas from the formal reference.
- `tools/sync_ct3_ct5_semantic.py` — derives the CT3-v1 through CT17-v1 graphs and concrete schemas from the formal reference.
- `tools/sync_semantic_manuscript_sections.py` — synchronizes all semantic CT1–CT17 sections into the numbered manuscript mirror.
- `MANUAL_REVIEW.md` — what still requires mathematical author review.

## Why JSON Schema is not enough

JSON Schema can validate local object shape, required fields, enums, and contract-instance structure. It cannot generally prove cross-object graph facts such as:

- consecutive presentation numbering and semantic ID validity;
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

## Identity and presentation order

For every tactic, `nodeNumber` and `transitionNumber` are presentation order only. Semantic IDs such as `CT1.certify.equivalence`, `CT2.decide.replacementCandidate`, `CT12.certify.decrease`, and `CT17.decide.arithmetic` are stable identities. A branch may skip later presentation numbers, and CT12's declared well-founded loop may return to an earlier one. The transition graph is authoritative for execution.
