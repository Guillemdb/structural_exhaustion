# structural_exhaustion

Reference manual and machine-centric Lean implementation of the 17 structural
exhaustion closure tactics.

## Run the CT1 through CT17 formal reference

`ct2_formal_reference` is a Lean library rather than a standalone CLI. Its
runtime model contains 17 exact sequential machines, 206 semantic nodes, 191
evidence-carrying transitions, 98 exact terminal types, and 96 executable
terminal instances. Every cross-tactic route carries the consumer's validated
Lean input and an explicit alignment proof. CT12 is the sole cyclic tactic; its
back edge is justified by a strict decrease consumed by well-founded recursion.

Prerequisites:

- `make`;
- Lean's `elan`, with `lake` available on `PATH`;
- either `uv`, or Python 3.10 or newer with `venv` and `pip`.

The recommended dependency-managed workflow is:

```bash
cd ct2_formal_reference
uv run --with-requirements requirements.txt make verify
uv run --with-requirements requirements.txt make test
```

With standard Python tooling, create and activate a virtual environment first:

```bash
cd ct2_formal_reference
python3 -m venv .venv
source .venv/bin/activate
python -m pip install -r requirements.txt
make verify
make test
```

On its first invocation, `lake` uses `lean-toolchain` to install and select Lean
`v4.31.0`. A successful `make verify` rebuilds the CT1--CT17 Lean library and
examples, regenerates the formal JSON and manuscript projections, checks every
JSON-referenced Lean declaration, rejects proof placeholders, validates all
graphs and schemas, and writes
`generated/ct1-lean-verification.json` through
`generated/ct17-lean-verification.json` with status `kernel_checked`.

The expected repository summary is:

```text
OK: 17 tactics, 206 semantic nodes, 191 typed transitions, 98 exact terminals, 96 executable instances
```

See [the CT1--CT17 reference README](ct2_formal_reference/README.md) for the
machine inventory, modular Lean API, tactic syntax, CT12 termination contract,
repository layout, and individual maintenance commands.
