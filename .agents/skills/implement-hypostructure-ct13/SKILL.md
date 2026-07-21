---
name: implement-hypostructure-ct13
description: Implement Hypostructure CT13 tiered-resource selection and canonical fallback. Use for first eligible primary payers, minimum-cost obstructions, tier-two schedules, resource-overlap detection, charge reconciliation, graph fallback resources, or PDE local/harmonic and gauge/cokernel splits.
---

# Implement Hypostructure CT13

Use CT13 when a proof first seeks an eligible primary payer, then selects a canonical minimum-cost obstruction, reconciles its tier-two resources, and compares total charge with demand.

## Establish the live contract

Read completely:

- `hypostructure/Hypostructure/CT13/{Spec,Capability,State,Search,Execution,Theorems,Automation}.lean`;
- the needed `Graph/CT13.lean` or `PDE/CT13.lean` adapter;
- `hypostructure/Hypostructure/Fixtures/CT13.lean`;
- CT13 rows in `migration/hypostructure/api-feature-matrix.csv`, relevant PDE rows, and barrel imports.

Respect the exact migration status. A Graph adapter marked `implemented` is not yet `kernel_checked`, and a `planned` row is not callable; a source file or barrel import alone does not upgrade either. If any required layer lacks reviewed evidence, pause the application and use `$extend-hypostructure-framework`. Do not implement fallback selection or reconciliation as application-local theorem code.

## Supply predecessor-owned primitives

Define `CT13.Spec` with predecessor-dependent `Payer`, `Obstruction`, and `Resource`, plus primitive `Eligible`, `obstructionCost`, `payerResource`, `charge`, and `demand` semantics.

Define `CT13.Capability` with typed `Core.Residual.Query` ledger reads for:

- the ordered tier-one payer enumeration;
- a nonempty `ObstructionSchedule` consisting of the first/default obstruction and a nodup remainder;
- the ordered tier-two payer enumeration for each inherited obstruction.

Also provide eligibility decisions, resource decidable equality, and the polynomial work bound. Do not provide a fallback, tier-two choice, overlap pair, ledger, total capacity, or terminal.

Every queried schedule must already belong to the literal predecessor. Use Core query combinators to expose it; never manufacture a node-local payer subtype, obstruction image, or resource assignment.

## Execute canonical fallback and reconciliation

1. Fix payer, obstruction, and tier-two orders explicitly; they are observable execution data.
2. Run the first-eligible payer scan.
3. On exhaustive absence, let CT13 compute the stable first minimum obstruction. A strictly lower cost replaces the current selection; ties retain the earlier obstruction.
4. Let CT13 form the selected tier-two product schedule and select the first pair of distinct payers sharing a resource.
5. If overlap is absent, let CT13 build the exact ordered reconciliation entries and sum their charges.
6. Let Core compare generated capacity with demand.
7. Invoke `CT13.execute` or `ct13_execute`; consume the typed generated outcome rather than rerunning any step.

## Discharge every outcome

Handle exactly:

- `.tierOne`: first eligible payer and ineligible prefix;
- `.overlap`: verified fallback plus the first distinct same-resource pair and clean prefix;
- `.deficit`: verified reconciliation ledger with `capacity < demand`;
- `.reconciled`: the same generated ledger with `demand <= capacity`.

Retain and consume `FallbackClaim` and `ReconciliationClaim`; do not copy their facts into a replacement record. Prove exact predecessor, `OutcomeClaim`, exact trace, terminal exhaustiveness, deterministic totality, and polynomial work. Bound work by the tier-one scan, obstruction comparisons, the square of the summed tier-two cardinalities, ledger construction, and final comparison.

## Use domain adapters honestly

- Graph: use `Graph.CT13.tieredSpec` and `tieredCapability` only after `graph.ct13` reaches the required reviewed status.
- PDE: use `PDE.CT13.tieredSpec` and `tieredCapability` for represented local/harmonic, gauge/decay/cokernel, or carrier fallback semantics over explicit schedules.

The PDE adapter does not prove analytic decomposition or resource adequacy. Supply those as exact semantic laws or named allowed contracts. Never turn an infinite resource search into a finite CT13 schedule without a theorem establishing that reduction.

## Validate completion

Keep `Fixtures/CT13.lean` covering all four terminals, primary order, first-minimum ties, pair order, exact ledgers, traces, checks, and both domain adapters. Run focused source/fixture checks and the package, import-firewall, and trust gates. Update migration status only from fresh evidence.
