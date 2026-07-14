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
lake env lean EvenCycleExample/CT2Audit.lean
lake env lean EvenCycleExample/CT12MaximalMatching.lean
lake env lean EvenCycleExample/CT14HighCenterDeletionCharge.lean
```

## API boundary

- `Problem.lean` selects the graph layer's canonical
  `Graph.EndpointParityCycle.Profile.evenCycle`. Its embedded
  `Graph.MinimumDegreeCycle.StaticInput` remains the single source for the
  problem, target, CT1 encoding, and deletion-only CT2 API.
- `CT1Instance.lean` only publishes names for that generated CT1 API.
- `CT6Instance.lean`, `CT9Instance.lean`, and `CT6CT9.lean` publish thin names
  for the generated greedy path, CT6 active ledger, typed CT6→CT9 route,
  parity overload, endpoint positions, and Mathlib chord-cycle certificate.
- `Run.lean` exposes the theorem and the final CT1 validation run.
- `CT2Audit.lean` instantiates the packed proper-subgraph CT2 profile and the
  dart-deletion CT2 capability, exposing the no-proper-core theorem, exact
  constant-work trace, and degree-three endpoint invariant.
- `CT3SeriesReduction.lean` implements the textbook Duffin parity-series
  response table and independently instantiates the certificate-driven
  boundaried replacement profile, including its compression terminal, typed
  trace, minimality contradiction, totality, and one-check work bound.
- `CT1InducedEdge.lean` is the external `K₄` fixture for the graph layer's
  reusable induced-edge CT1 profile, pinning its terminal, exact trace, and
  constant work count.
- `CT12MaximalMatching.lean` is the external `K₄` fixture for
  `Graph.MaximumMatching`, whose graph-owned implementation specializes the
  induced-path packing profile to order two and proves the maximum, partition,
  CT12 audit, and edgeless-remainder results.
- `CT14HighCenterDeletionCharge.lean` instantiates
  `Graph.HighCenterDeletionCharge` on the textbook `K₃,₄`. Its three
  degree-four vertices are deleted, the retained four-vertex graph is proved
  edgeless and internal-three-core-free, and the exact generic
  `21 * assignedSurplus + receiverOverload` theorem is reused without HSS.
- `Concrete.lean` runs the pipeline on Mathlib's complete graph on four
  explicitly scheduled vertices and checks the exact terminals, traces,
  maximal path, and cycle.

The reusable-code dependency direction is strictly one-way:

```text
examples/even_cycle  --->  lean/StructuralExhaustion  --->  Mathlib
          |------------------------------------------->  Mathlib
```
