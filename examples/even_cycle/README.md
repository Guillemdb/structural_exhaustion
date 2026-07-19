# Even-cycle worked example

This is an independent Lean package using the framework exactly as an
external application would:

```toml
[[require]]
name = "mathlib"
scope = "leanprover-community"
git = "https://github.com/leanprover-community/mathlib4"
rev = "v4.31.0"

[[require]]
name = "structural_exhaustion"
path = "../../lean"
```

The direct Mathlib dependency uses the same scoped v4.31.0 pin as the
framework. The example does not define a second graph representation: every
graph is a Mathlib `SimpleGraph`, bundled with
`StructuralExhaustion.Graph.FiniteInput` only to make the machine schedule and
adjacency decider explicit.

## Build

From the repository root:

```bash
make mathlib-cache
make framework-build
make even-cycle-example-build
```

Or directly:

```bash
cd examples/even_cycle
lake update
lake build
```

The package entry point is `EvenCycleExample.lean`. Individual surfaces can
be checked with:

```bash
lake env lean EvenCycleExample/Run.lean
lake env lean EvenCycleExample/Concrete.lean
```

## API boundary

- `Problem.lean` selects the graph layer's canonical
  `Graph.EndpointParityCycle.Profile.evenCycle`. This is the only
  problem-specific selection: it fixes the minimum-degree threshold and the
  even-length predicate.
- `CT1Instance.lean`, `CT6Instance.lean`, `CT9Instance.lean`, and
  `CT6CT9.lean` publish names for the profile-generated CT1, CT6, registered
  CT6→CT9 route, parity overload, and chord-cycle certificate.
- `Run.lean` exposes the public theorem and final CT1 validation run without
  defining a search, route, capability, or certificate constructor.
- `Concrete.lean` runs the pipeline on Mathlib's complete graph on four
  explicitly scheduled vertices and checks the exact terminals, traces,
  maximal path, and cycle.

The reusable-code dependency direction is strictly one-way:

```text
examples/even_cycle  --->  lean/StructuralExhaustion  --->  Mathlib
          |------------------------------------------->  Mathlib
```
