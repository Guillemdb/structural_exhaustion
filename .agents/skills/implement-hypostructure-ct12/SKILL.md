---
name: implement-hypostructure-ct12
description: Implement Hypostructure CT12 well-founded structural peeling. Use for predecessor-owned peeling states, proof-carrying strict decreases, demand or tier residuals, finite list peeling, graph vertex schedules, PDE observable schedules, exact iteration traces, and bounded recursive exhaustion.
---

# Implement Hypostructure CT12

Use CT12 only when every recursive continuation carries a strict decrease that the framework runner consumes. CT12 owns the recursion; an application supplies local peeling semantics and one predecessor-owned initial state.

## Establish the live contract

Read completely:

- `hypostructure/Hypostructure/CT12/{Spec,Capability,State,Search,Execution,Theorems,Automation,ListPeeling}.lean`;
- the applicable `Graph/CT12.lean` or `PDE/CT12.lean` adapter;
- `hypostructure/Hypostructure/Fixtures/CT12.lean`;
- the `ct.ct12` and `graph.ct12` rows in `migration/hypostructure/api-feature-matrix.csv`, relevant PDE rows, and public barrel imports.

Check each layer independently. In particular, source presence does not upgrade a `planned` or merely `implemented` domain adapter to `kernel_checked`. If the required generic profile, domain adapter, fixture, or integration status is missing, stop application work and use `$extend-hypostructure-framework`. Never recreate a peeling loop, packing profile, or result type as application-local code.

## Define the indexed local semantics

Define `CT12.Spec` with:

- `State previous load` and `Peeled` for positive-load states;
- predecessor-indexed `DemandResidual` and `TierResidual` types;
- one local `peel` operation;
- `restorations`, returning nonempty `RestorationOptions` in policy order.

Each `Restoration` must be one of:

- `.continue next state decreases`, with `next < current load`;
- `.demand residual`;
- `.tier residual`.

The author defines the local option schedule, but the framework selects its first member, records membership and the selection equation, checks decrease, and owns all subsequent recursion and routing. Do not pass a selected branch separately.

Define `CT12.Capability.initial` as a `Core.Residual.Query` returning `InitialState spec`. The initial load and state must come from the literal predecessor. Supply only the polynomial envelope for `maximumChecks load = 4 * load + 1`.

## Run the well-founded machine

1. Choose the load measure before defining `peel`; it must bound the whole continuation chain.
2. Ensure every continuation state is indexed by its proved smaller load.
3. Keep restoration order deterministic and semantically justified.
4. Run `CT12.execute` or `ct12_execute`; never call `runLoop` from an application or write parallel recursion.
5. Consume the generated `Outcome`, `LoopTrace`, iteration count, and check count.

Use `CT12.ListPeeling.Profile` for an exact predecessor-owned finite list. It derives head/tail states, strict length decrease, linear work, exhausted terminal, exact iterations, and exact trace. If the proof needs maximum packing, saturation, restoration search, or another profile not present in the live source, treat it as a missing framework capability rather than encoding it in the application.

## Discharge every outcome

Handle exactly:

- `.exhausted`: a framework-generated load-zero `ExhaustedCertificate`;
- `.demand`: the supplied proof-carrying demand residual selected by the runner;
- `.tier`: the supplied proof-carrying tier residual selected by the runner.

Prove or reuse `OutcomeClaim`, predecessor retention, terminal exhaustiveness, `runLoop_terminates`, `iterations_le_initialLoad`, the exact check equation, exact trace length, deterministic execution, totality, and `checks_le_polynomial`. Route every demand and tier residual; do not relabel either as exhaustion.

Reject a recurrence whose local states are finite but whose global load does not strictly decrease. Reject any hidden frontier expansion not covered by the declared polynomial bound.

## Use domain adapters only at their reviewed status

- Graph: `Graph.CT12.vertexPeelingProfile` and `peelVertices` derive a list profile from the queried `FiniteObject` vertex schedule.
- PDE: `PDE.CT12.observablePeelingProfile` and `peelObservables` accept only an explicit finite observable-index schedule.

Neither adapter licenses graph-wide packing enumeration, uncountable scale search, or ambient PDE-state enumeration.

## Validate completion

Keep `Fixtures/CT12.lean` covering zero load, multi-step exhaustion, immediate demand, immediate tier, exact restoration order, iteration/check equations, list peeling, and Graph/PDE adapters. Run focused checks followed by package, import-firewall, and trust validation. Do not claim domain integration above its migration-ledger status.
