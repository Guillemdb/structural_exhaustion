---
name: implement-hypostructure-ct17
description: Implement Hypostructure CT17 bounded target thickening and survivor arithmetic. Use for predecessor-owned targets, offsets, scales, positions, finite compatibility scans, finite-block survivors, orbit target hits, graph bounded-target parameters, or PDE scale, shell, and modulation arithmetic.
---

# Implement Hypostructure CT17

Use CT17 only for explicit bounded schedules carried by the predecessor. It audits target-offset compatibility, splits the selected scale at a finite limit, and performs either finite-block survivor enumeration or one declared orbit-slice comparison.

## Establish the live contract

Read completely:

- `hypostructure/Hypostructure/CT17/{Spec,Capability,State,Search,Execution,Theorems,Automation}.lean`;
- the applicable `Graph/CT17.lean` or `PDE/CT17.lean` adapter;
- `hypostructure/Hypostructure/Fixtures/CT17.lean`;
- CT17 rows in `migration/hypostructure/api-feature-matrix.csv`, relevant PDE route/row requirements, and barrel imports.

Check reviewed status, fresh fixtures, and intended import surface. A source file that is not integrated or a planned CT17-to-CT12 route is not application-ready. If a required layer is absent or below the needed status, stop and use `$extend-hypostructure-framework`; use `$implement-hypostructure-route` for an endpoint-ready transition gap. Never implement an open-ended scale search or local survivor machine.

## Supply bounded predecessor-owned primitives

Define `CT17.Spec` with predecessor-dependent `Target`, `Offset`, scale-indexed `Position`, and `Value`, plus primitive `targetValue`, `blockValue`, `orbitValue`, and `Compatible` semantics.

Define `CT17.Capability` with typed `Core.Residual.Query` ledger reads for:

- exact target and offset enumerations;
- the finite admissible scale enumeration;
- one selected scale and a proof that it belongs to that exact enumeration;
- the position enumeration at every queried scale;
- the finite/orbit cutoff.

Also provide compatibility decisions, value decidable equality, and a polynomial work envelope. Do not provide a selected compatibility branch, finite/orbit verdict, survivor list, target hit, orbit values, outcome, or trace.

All schedules and the selected scale must be reads from the same literal predecessor. Do not materialize an infinite orbit, synthesize scales by recursion, or create application-local target/offset products.

## Execute the bounded arithmetic

1. Derive every finite schedule and cutoff from the source theorem.
2. Fix target-major, offset-minor order; first hits depend on it.
3. Let CT17 scan for the first incompatible target-offset pair.
4. On complete compatibility, let Core decide `selectedScale <= limit` versus `limit < selectedScale`.
5. In the finite branch, let CT17 test every inherited position against the complete pair schedule, construct the exact nodup survivor list, and split empty from nonempty.
6. In the orbit branch, let CT17 scan the declared orbit slice for the first target value; on failure it computes only the exact offset-indexed orbit-value list.
7. Run `CT17.execute` or `ct17_execute` and consume the generated evidence.

## Discharge every outcome

Handle exactly:

- `.incompatibility`: first incompatible pair and compatible prefix;
- `.exhausted`: scheduled compatibility, finite scale, exact survivor enumeration, and no survivor;
- `.survivors`: scheduled compatibility, finite scale, exact nonempty enumeration, canonical first survivor, and complete survival equivalence;
- `.targetHit`: orbit scale and first exact target-value hit;
- `.orbit`: orbit scale, exact computed values, and exhaustive target avoidance.

Prove predecessor retention, scale membership, `OutcomeClaim`, exact trace, terminal exhaustiveness, deterministic totality, branch-exact checks, and `checks_le_polynomial`. Bound the target-offset product, all position-by-pair scans, and orbit materialization. Test scale zero, equality with the cutoff, and the first scale above it.

## Use domain adapters without expanding the universe

- Graph: use `Graph.CT17.boundedTargetSpec` and `boundedTargetCapability` for bounded lengths, offsets, shells, or survivor parameters evaluated against the queried finite graph.
- PDE: use `PDE.CT17.boundedScaleSpec` and `boundedScaleCapability` for represented finite scale, shell, modulation, or compactification arithmetic.

The PDE adapter does not make a continuum enumerable. An analytic reduction to the finite schedules must be an exact theorem or named allowed contract.

## Validate completion

Keep `Fixtures/CT17.lean` covering all five terminals, first-hit orders, survivor exactness, orbit values, scale boundaries, exact checks and traces, Graph, and PDE. Run focused source and fixture checks, then package, import-firewall, and trust validation. Do not claim a planned CT17 route or PDE-row integration from the CT fixture alone.
