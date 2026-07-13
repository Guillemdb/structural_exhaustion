# Mantel worked example

This independent Lake package imports the reusable structural-exhaustion
framework and proves Mantel's theorem for a Mathlib `SimpleGraph` bundled with
deterministic finite input:

```lean
object.edgeCount ≤ object.input.vertices.card ^ 2 / 4
```

The problem layer supplies only the graph and a `CliqueFree 3` proof. The
framework owns the degree identities, Cauchy--Schwarz argument, CT11
negative-budget localization, and triangle-free contradiction.

From the repository root:

```bash
make mathlib-cache
make mantel-example-build
```

Or directly:

```bash
cd examples/mantel
lake update
lake build
```

`Concrete.lean` pins the exact CT11 trace on `K₄` and invokes the completed
theorem on the triangle-free cycle `C₅`.
