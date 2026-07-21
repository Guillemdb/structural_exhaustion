---
name: implement-hypostructure-ct9
description: Implement Hypostructure CT9 exact finite label-fibre overload. Use for pigeonhole arguments over a residual-owned item schedule, first overloaded fibres, complete bounded partitions, capacity-one collisions, parity profiles, graph role labels, or PDE packet and profile capacities.
---

# Implement Hypostructure CT9

Use CT9 to partition the exact incoming item schedule by a complete finite label family and select the first overloaded fibre or certify every fibre is within capacity.

## Gate the live contract

1. Read row `ct.ct9` in `migration/hypostructure/api-feature-matrix.csv`.
2. Read `hypostructure/Hypostructure/CT9/{Spec,Capability,State,Search,Execution,Theorems,Automation}.lean` and `Profiles.lean`.
3. Inspect `hypostructure/Hypostructure/{Graph,PDE}/CT9.lean` and `hypostructure/Hypostructure/Fixtures/CT9.lean`.
4. Confirm live declarations and fresh `.olean` evidence, for example with `cd hypostructure && lake env lean Hypostructure/Fixtures/CT9.lean`. Check downstream route rows independently; a CT endpoint does not make a route executable.

The generic, Graph, PDE, capacity-one, and parity slices are currently present. Specialized CT9-to-CT7 and CT9-to-CT9 semantic routes are currently planned rather than kernel-checked. Recheck live status; never recreate a missing route or CT surface in an application. Use `$extend-hypostructure-framework`.

## Supply exact partition semantics

Define `CT9.Spec` with predecessor-indexed `Item` and `Label`, the primitive label map, and capacity.

Define `CT9.Capability` with:

- `items`, a `Core.Residual.Query` for the exact duplicate-free incoming item enumeration;
- `labels`, a complete finite label enumeration for each predecessor; and
- a polynomial envelope for `localCheckBound`.

The item schedule must be queried from the literal predecessor. The label schedule is intentionally an author-provided complete semantic universe, not a replacement item carrier; pin its order because it determines the first overload. Do not supply fibres, a partition, a selected label, or a bounded certificate.

Prefer `capacityOneSpec` and `ParityCapacityOneProfile` for capacity-one or rank-parity arguments. Use `runOverloadedOfTotalCapacityLtCardinality`, `sameLabelPairOfCapacityOne`, or `runParityCapacityOneOfThreeLeCardinality` to package a forced generated run instead of manually applying pigeonhole reasoning to a rebuilt partition.

Record label/capacity semantics, the item query, complete label universe, rank, and work proof as author primitives or inferred inputs. Record the partition, fibres, first-overload search, typed outcome, selected pair, terminal, trace, and accumulated stage as framework outputs in `Core.Provision`.

## Execute and consume the dichotomy

1. Call `CT9.execute spec capability previous` or `executeParityCapacityOne`.
2. For `.overloaded`, consume `SelectedOverload`, `OverloadResidual`, and any framework-derived `SameLabelPair`.
3. For `.bounded`, consume `BoundedCertificate` and the exact partition/cardinality theorems; never recompute all fibres.
4. Prove predecessor retention, `result.verified`, `result.trace_exact`, overload/bounded terminal forcing, `run_total`, determinism, outcome exhaustiveness, `checks_le_limit`, and `checks_le_polynomial`.

For graphs, use `Graph.CT9.roleSpec`, `roleCapability`, or `parityProfile`. For PDEs, use `PDE.CT9.packetSpec`, `packetCapability`, or `parityProfile` against a queried represented state.

Use `Fixtures/CT9.lean` as the minimum: test overload and bounded terminals, pinned first label and exact work, partition cardinality, forced capacity-one and parity pairs, and thin Graph and PDE adapters.

## Practicality and carrier rules

The exact bound is `labels.card * (items.card + 1)`. Enumerate labels and scan the supplied items only. Never enumerate partitions or subsets, replace the incoming item family, or construct a node-local capacity token collection. A missing CT6-to-CT9, CT9-to-CT7, or CT9-to-CT9 transition belongs to framework routing.
