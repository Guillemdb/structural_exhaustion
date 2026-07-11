# CT1 through CT17 formal reference implementation

This directory contains the machine-centric Lean implementation of all 17
structural-exhaustion tactics. The Lean library, semantic JSON graphs,
executable examples, manuscript diagrams, and generated verification records
describe the same runtime machines.

The current repository contains:

- 17 tactics;
- 206 semantic nodes;
- 191 evidence-carrying transitions;
- 98 exact terminal types;
- 96 executable terminal instances.

Every cross-tactic handoff carries the consumer's exact validated `Input` and
an explicit alignment proof. There are no untyped route tags or placeholder
`CTkDatum` fields. CT12 is the sole cyclic machine; its back edge carries a
`DecreasedState` proof and its executor is well-founded recursion on a recorded
natural-valued load.

## Run everything

Prerequisites:

- `make`;
- [elan](https://github.com/leanprover/elan), with `lake` on `PATH`;
- `uv` (recommended), or Python 3.10+ with `venv` and `pip`.

From the repository root, the recommended dependency-managed workflow is:

```bash
cd ct2_formal_reference
uv run --with-requirements requirements.txt make verify
uv run --with-requirements requirements.txt make test
```

The first run may download the Python dependencies and the Lean toolchain
pinned in `lean-toolchain` (`v4.31.0`). A successful `make verify`:

1. regenerates all CT1--CT17 semantic specifications and graph projections;
2. regenerates the combined JSON-to-Lean binding check;
3. synchronizes the machine-centric manuscript sections and numbered catalog;
4. builds every tactic, node module, theorem, tactic macro, and example;
5. rejects authored `sorry`, `admit`, and `axiom` declarations;
6. resolves every Lean declaration referenced by the JSON graphs;
7. writes `generated/ct1-lean-verification.json` through
   `generated/ct17-lean-verification.json`, each with status `kernel_checked`;
8. validates schemas, exact paths, terminal coverage, cycle policy, and source
   references; and
9. refreshes `SHA256SUMS`.

The successful repository summary is:

```text
OK: 17 tactics, 206 semantic nodes, 191 typed transitions, 98 exact terminals, 96 executable instances
```

To use standard Python tooling instead of `uv`:

```bash
cd ct2_formal_reference
python3 -m venv .venv
source .venv/bin/activate
python -m pip install -r requirements.txt
make verify
make test
```

## Useful commands

Run these from `ct2_formal_reference`:

```bash
make specs      # regenerate CT1--CT17 formal JSON and the manifest
make bindings   # regenerate BindingCheck.lean and graph projections
make catalog    # synchronize manuscript sections and the CT1--CT17 catalog
make build      # run lake build for every Lean module and example
make validate   # validate both formal repositories and every schema
make verify     # regenerate, build, kernel-check, validate, and checksum
make test       # validate, then run the Python regression suite
make checksums  # refresh SHA256SUMS
```

Lean-only smoke test:

```bash
lake build
lake env lean StructuralExhaustion/Generated/BindingCheck.lean
```

Validate without regenerating artifacts:

```bash
python3 tools/validate_repository.py
python3 ../framework/json_schemas/tools/validate_tactics.py \
  ../framework/json_schemas/data/ct1-ct17.numbered.json
```

## Machine inventory

| Tactic | Independent core-plan fields | Exact terminals |
|---|---|---|
| CT1 | scope, equivalence, realization, payload | scope, C1, CT2, CT3, CT4, CT5, CT6, CT17 |
| CT2 | interface, deletion, replacement candidate, context, survivor | scope, C2 deletion, C2 replacement, CT3 context, CT3 response, CT10 |
| CT3 | scope, equivalence, compression, defect, table | scope, C2, C3, C5, CT7, CT8, CT12 |
| CT4 | scope, assignment, availability, fibres, comparison | scope, C4, CT9, CT13, CT14 |
| CT5 | scope, locality, deficit, summation, comparison | scope, C4, CT4, CT11, CT14 |
| CT6 | scope, definition, activity, active ledger, dormant routing | scope, C1, CT3, CT4, CT7, CT9, CT10 |
| CT7 | scope, context, realization, distinction, defect, neutral | scope, C1, C2, C3, CT3, CT10, CT12, CT16 |
| CT8 | scope, equivalence, repetition, response, routing | scope, C2, C5, CT3, CT7, CT10 |
| CT9 | scope, fibre, overload, extraction, routing | scope, C1, CT4, CT7, CT8, CT10 |
| CT10 | scope, labels, classification, direct, promotion, promoted routing | scope, C5, CT3, CT7, CT15 |
| CT11 | scope, decomposition, admissibility, localization, routing | scope, CT1, CT7, CT10, CT14 |
| CT12 | scope, measure, saturation, peel, restoration, decrease | scope, C4, CT4, CT13 |
| CT13 | scope, availability, tier one, tier-one routing, fallback, reconciliation, comparison, routing | scope, C4, CT4, CT9, CT14 |
| CT14 | scope, bounds, multiplicity, comparison | scope, C4, CT9, CT10 |
| CT15 | scope, rank, rank drop, dependence routing, ledger, comparison | scope, C4, CT3, CT4, CT7, CT16 |
| CT16 | support, scope, closed type, equality | scope, C2, CT3, CT10 |
| CT17 | scope, compatibility, separation, block, scale, survivors, arithmetic | scope, C1, C5, CT3, CT8, CT10, CT14 |

CT11 is intentionally route-only. CT12 is intentionally cyclic. Every other
machine is acyclic. These properties are checked by the repository validator,
not merely stated in documentation.

## Modular Lean API

Each tactic follows the same dependency direction:

```text
Interface (cycle-free validated entry)
        ↓
Types → independent Nodes/* modules
   └──────────────┬──────────────┘
                Graph → Execution → Theorems → Automation
```

- `Interface.lean` contains only the import-cycle-free entry contract.
- `Types.lean` defines indexed predecessor states, certificates, exact
  downstream payloads, `Port`, and `HandoffPlan`.
- each `Nodes/*.lean` file owns one local `Contract`, `Plan`, and `run`; a
  branching node also owns its proof-carrying `Decision`;
- `Graph.lean` defines evidence-indexed edges and paths;
- `Execution.lean` interprets a complete `CorePlan` and derives the visible
  trace from the typed path;
- `Theorems.lean` proves soundness, trace validity, totality relative to the
  supplied plans, and terminal exhaustiveness; and
- `Automation.lean` exposes the tactic syntax.

This boundary lets a later implementation replace or strengthen one node while
reasoning only from its immediate input contract to its declared output. The
rest of the tactic remains protected by Lean's types.

### CT12 termination contract

CT12 separates peeling, restoration, and descent:

```text
saturation → peel certification → restoration → decrease certification
     ▲                                      │
     └──────────── strictly smaller load ───┘
```

`RestoredState` does not license recursion. The back edge requires
`DecreasedState`, whose `decreases : next < load` field is consumed by
`runLoop`'s termination proof. `Graph.Edge.loop_decreases` proves that every
inhabitant of the back-edge type contains such a strict inequality.

## Using a tactic from Lean

After constructing a framework, validated input, total node plans, port, and
handoff proof, every CT uses the same syntax. For CT17:

```lean
def result : CT17.ExecutionResult framework input port :=
  ct17_execute input using corePlan with port via handoffPlan

example : CT17.OutcomeClaim result.outcome := by
  ct17 input using corePlan with port via handoffPlan

example : ∃ result : CT17.ExecutionResult framework input port,
    CT17.OutcomeClaim result.outcome ∧
      @CT17.Graph.ValidTrace framework input result.trace := by
  ct17_total input using corePlan with port via handoffPlan
```

Replace `17` with any tactic number from 1 through 17. These macros apply the
verified interpreter theorems. They do not invent mathematical witnesses:
`run_total` is totality relative to the supplied total node plans, not an
automatic completeness theorem for arbitrary objects.

## Executable coverage and layout

`StructuralExhaustion/Examples/CT1Toy.lean` through `CT17Toy.lean` exercise
every declared terminal. CT12's C4 example traverses the back edge once before
closing. Several examples also extract an exact consumer input from an executed
producer outcome and run the downstream tactic.

Key paths:

```text
ct2_formal_reference/
├── StructuralExhaustion/CT1/ ... CT17/
├── StructuralExhaustion/Examples/CT1Toy.lean ... CT17Toy.lean
├── StructuralExhaustion/Generated/BindingCheck.lean
├── framework/CT1/ ... CT17/
├── instances/ct1/ ... ct17/
├── schemas/
├── generated/
├── tools/
├── tests/
├── lakefile.toml
└── lean-toolchain
```

When extending a machine, update its Lean contracts and exhaustive example
first, update the corresponding generator and manuscript excerpt, then run
`make verify` and `make test`.
