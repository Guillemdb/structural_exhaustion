# Greedy-coloring worked example

This independent Lake package imports the reusable structural-exhaustion
framework and proves the Mathlib-native theorem

```lean
object.graph.Colorable (object.maxDegree + 1)
```

for every `Graph.FiniteObject`. The example defines no coloring algorithm,
peeling recursion, capacity argument, or CT capability. Those live in the
framework's `Graph.GreedyColoring`, `CT4.Cardinality`, and
`CT12.ListPeeling` modules.

From the repository root:

```bash
make mathlib-cache
make greedy-coloring-example-build
```

Or directly:

```bash
cd examples/greedy_coloring
lake update
lake build
```

`Concrete.lean` executes the complete CT12 → CT4 → CT1 architecture on
Mathlib's complete graph `K₄`, checks the deterministic coloring, and pins the
exact CT12, CT4, and CT1 terminals and traces.
