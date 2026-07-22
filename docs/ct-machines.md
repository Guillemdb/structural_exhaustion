# Automation-first Lean CT inventory

Generated from the compiled `StructuralExhaustion.Canonical` registry.

| Tactic | Nodes | Edges | Terminals | Author definitions | Derived operations | Residuals |
|---|---:|---:|---:|---:|---:|---:|
| CT1 | 5 | 4 | 2 | 10 | 24 | 3 |
| CT2 | 7 | 6 | 4 | 22 | 25 | 3 |
| CT3 | 9 | 8 | 4 | 19 | 7 | 3 |
| CT4 | 9 | 8 | 4 | 9 | 9 | 4 |
| CT5 | 8 | 7 | 4 | 11 | 8 | 4 |
| CT6 | 4 | 3 | 2 | 7 | 14 | 3 |
| CT7 | 6 | 5 | 3 | 6 | 5 | 2 |
| CT8 | 6 | 5 | 3 | 8 | 6 | 3 |
| CT9 | 5 | 4 | 2 | 5 | 32 | 2 |
| CT10 | 8 | 7 | 3 | 8 | 7 | 3 |
| CT11 | 6 | 5 | 2 | 4 | 6 | 3 |
| CT12 | 8 | 8 | 3 | 6 | 7 | 3 |
| CT13 | 9 | 8 | 4 | 14 | 6 | 4 |
| CT14 | 9 | 8 | 4 | 7 | 6 | 4 |
| CT15 | 8 | 7 | 3 | 6 | 9 | 3 |
| CT16 | 7 | 6 | 3 | 8 | 3 | 3 |
| CT17 | 10 | 9 | 5 | 14 | 9 | 4 |

## Per-node automation contracts

### CT1

- `CT1.entry` — `definitional`; author 0, predecessor 1, framework 0, outputs 1, manual obligations 0.
- `CT1.certify.equivalence` — `definitional`; author 3, predecessor 0, framework 1, outputs 1, manual obligations 0.
- `CT1.decide.realization` — `finiteSearch`; author 10, predecessor 1, framework 4, outputs 3, manual obligations 0.
- `CT1.terminal.c1` — `genericTheorem`; author 0, predecessor 1, framework 1, outputs 1, manual obligations 0.
- `CT1.terminal.avoiding` — `genericTheorem`; author 0, predecessor 1, framework 1, outputs 1, manual obligations 0.

### CT2

- `CT2.entry` — `definitional`; author 0, predecessor 1, framework 0, outputs 1, manual obligations 0.
- `CT2.decide.deletion` — `verifiedComputation`; author 3, predecessor 1, framework 3, outputs 3, manual obligations 0.
- `CT2.search.replacements` — `finiteSearch`; author 12, predecessor 1, framework 5, outputs 5, manual obligations 0.
- `CT2.terminal.c2.deletion` — `genericTheorem`; author 0, predecessor 1, framework 1, outputs 1, manual obligations 0.
- `CT2.terminal.c2.replacement` — `genericTheorem`; author 0, predecessor 1, framework 1, outputs 1, manual obligations 0.
- `CT2.terminal.residual.separatingContext` — `genericTheorem`; author 0, predecessor 1, framework 1, outputs 1, manual obligations 0.
- `CT2.terminal.residual.criticality` — `genericTheorem`; author 0, predecessor 1, framework 1, outputs 1, manual obligations 0.

### CT3

- `CT3.entry` — `definitional`; author 0, predecessor 2, framework 0, outputs 1, manual obligations 0.
- `CT3.compute.exact-vector` — `definitional`; author 1, predecessor 1, framework 1, outputs 1, manual obligations 0.
- `CT3.search.compression` — `finiteSearch`; author 8, predecessor 1, framework 3, outputs 3, manual obligations 0.
- `CT3.validate.table` — `finiteSearch`; author 5, predecessor 1, framework 1, outputs 3, manual obligations 0.
- `CT3.lookup.exact-row` — `finiteSearch`; author 4, predecessor 1, framework 3, outputs 3, manual obligations 0.
- `CT3.terminal.compression` — `genericTheorem`; author 0, predecessor 1, framework 1, outputs 1, manual obligations 0.
- `CT3.terminal.distinguishing-context` — `genericTheorem`; author 0, predecessor 1, framework 1, outputs 1, manual obligations 0.
- `CT3.terminal.known-row` — `genericTheorem`; author 0, predecessor 1, framework 1, outputs 1, manual obligations 0.
- `CT3.terminal.novel-row` — `genericTheorem`; author 0, predecessor 1, framework 1, outputs 1, manual obligations 0.

### CT4

- `CT4.entry` — `definitional`; author 0, predecessor 0, framework 0, outputs 1, manual obligations 0.
- `CT4.compute.assignment` — `finiteSearch`; author 3, predecessor 1, framework 2, outputs 1, manual obligations 0.
- `CT4.search.availability` — `finiteSearch`; author 1, predecessor 1, framework 1, outputs 3, manual obligations 0.
- `CT4.compute.fibres` — `verifiedComputation`; author 4, predecessor 1, framework 1, outputs 3, manual obligations 0.
- `CT4.decide.capacity` — `verifiedComputation`; author 3, predecessor 1, framework 1, outputs 3, manual obligations 0.
- `CT4.terminal.residual.missingPayer` — `genericTheorem`; author 0, predecessor 1, framework 1, outputs 1, manual obligations 0.
- `CT4.terminal.residual.overloadedFibre` — `genericTheorem`; author 0, predecessor 1, framework 1, outputs 1, manual obligations 0.
- `CT4.terminal.c4` — `genericTheorem`; author 0, predecessor 1, framework 1, outputs 1, manual obligations 0.
- `CT4.terminal.residual.capacity` — `genericTheorem`; author 0, predecessor 1, framework 1, outputs 1, manual obligations 0.

### CT5

- `CT5.entry` — `definitional`; author 0, predecessor 0, framework 0, outputs 1, manual obligations 0.
- `CT5.search.deficit` — `finiteSearch`; author 6, predecessor 0, framework 2, outputs 3, manual obligations 0.
- `CT5.compute.summation` — `verifiedComputation`; author 7, predecessor 1, framework 1, outputs 1, manual obligations 0.
- `CT5.decide.comparison` — `verifiedComputation`; author 2, predecessor 1, framework 0, outputs 4, manual obligations 0.
- `CT5.terminal.residual.localDeficit` — `genericTheorem`; author 0, predecessor 1, framework 1, outputs 1, manual obligations 0.
- `CT5.terminal.c4` — `genericTheorem`; author 0, predecessor 1, framework 1, outputs 1, manual obligations 0.
- `CT5.terminal.residual.chargeLedger` — `genericTheorem`; author 0, predecessor 1, framework 1, outputs 1, manual obligations 0.
- `CT5.terminal.residual.aggregate` — `genericTheorem`; author 0, predecessor 1, framework 1, outputs 1, manual obligations 0.

### CT6

- `CT6.entry` — `definitional`; author 0, predecessor 0, framework 0, outputs 1, manual obligations 0.
- `CT6.search.firstFailure` — `finiteSearch`; author 5, predecessor 0, framework 2, outputs 3, manual obligations 0.
- `CT6.terminal.residual.firstFailure` — `genericTheorem`; author 0, predecessor 1, framework 1, outputs 1, manual obligations 0.
- `CT6.terminal.residual.activeLedger` — `genericTheorem`; author 0, predecessor 1, framework 1, outputs 1, manual obligations 0.

### CT7

- `CT7.entry` — `definitional`; author 0, predecessor 1, framework 0, outputs 1, manual obligations 0.
- `CT7.search.realization` — `finiteSearch`; author 3, predecessor 1, framework 1, outputs 3, manual obligations 0.
- `CT7.search.distinction` — `finiteSearch`; author 2, predecessor 1, framework 1, outputs 3, manual obligations 0.
- `CT7.terminal.certificate.realization` — `genericTheorem`; author 0, predecessor 1, framework 1, outputs 1, manual obligations 0.
- `CT7.terminal.residual.distinguishing` — `genericTheorem`; author 0, predecessor 1, framework 1, outputs 1, manual obligations 0.
- `CT7.terminal.certificate.neutrality` — `genericTheorem`; author 0, predecessor 1, framework 1, outputs 1, manual obligations 0.

### CT8

- `CT8.entry` — `definitional`; author 0, predecessor 2, framework 0, outputs 1, manual obligations 0.
- `CT8.search.orderedRepeatedType` — `finiteSearch`; author 2, predecessor 1, framework 1, outputs 3, manual obligations 0.
- `CT8.compare.responses` — `finiteSearch`; author 3, predecessor 1, framework 1, outputs 3, manual obligations 0.
- `CT8.terminal.certificate.noRepetition` — `genericTheorem`; author 0, predecessor 1, framework 1, outputs 1, manual obligations 0.
- `CT8.terminal.residual.removal` — `genericTheorem`; author 0, predecessor 1, framework 1, outputs 1, manual obligations 0.
- `CT8.terminal.residual.responseSeparation` — `genericTheorem`; author 0, predecessor 1, framework 1, outputs 1, manual obligations 0.

### CT9

- `CT9.entry` — `definitional`; author 0, predecessor 2, framework 0, outputs 1, manual obligations 0.
- `CT9.compute.partition` — `definitional`; author 0, predecessor 0, framework 0, outputs 1, manual obligations 0.
- `CT9.search.firstOverload` — `finiteSearch`; author 3, predecessor 1, framework 3, outputs 3, manual obligations 0.
- `CT9.terminal.residual.overload` — `genericTheorem`; author 0, predecessor 1, framework 1, outputs 1, manual obligations 0.
- `CT9.terminal.certificate.bounded` — `genericTheorem`; author 0, predecessor 1, framework 1, outputs 1, manual obligations 0.

### CT10

- `CT10.entry` — `definitional`; author 0, predecessor 2, framework 0, outputs 1, manual obligations 0.
- `CT10.compute.classTable` — `definitional`; author 0, predecessor 0, framework 0, outputs 1, manual obligations 0.
- `CT10.search.direct` — `finiteSearch`; author 3, predecessor 0, framework 1, outputs 3, manual obligations 0.
- `CT10.search.firstMissing` — `finiteSearch`; author 3, predecessor 2, framework 3, outputs 3, manual obligations 0.
- `CT10.compute.promotion` — `definitional`; author 0, predecessor 1, framework 0, outputs 1, manual obligations 0.
- `CT10.terminal.residual.direct` — `genericTheorem`; author 0, predecessor 1, framework 1, outputs 1, manual obligations 0.
- `CT10.terminal.residual.promoted` — `genericTheorem`; author 0, predecessor 1, framework 1, outputs 1, manual obligations 0.
- `CT10.terminal.certificate.exhaustive` — `genericTheorem`; author 0, predecessor 1, framework 1, outputs 1, manual obligations 0.

### CT11

- `CT11.entry` — `definitional`; author 0, predecessor 3, framework 0, outputs 1, manual obligations 0.
- `CT11.compute.decomposition` — `definitional`; author 0, predecessor 0, framework 0, outputs 1, manual obligations 0.
- `CT11.search.admissibilityGap` — `finiteSearch`; author 2, predecessor 2, framework 1, outputs 3, manual obligations 0.
- `CT11.search.localNegativeBudget` — `finiteSearch`; author 1, predecessor 4, framework 1, outputs 1, manual obligations 0.
- `CT11.terminal.residual.admissibilityGap` — `genericTheorem`; author 0, predecessor 1, framework 1, outputs 1, manual obligations 0.
- `CT11.terminal.residual.localizedDeficit` — `genericTheorem`; author 0, predecessor 1, framework 1, outputs 1, manual obligations 0.

### CT12

- `CT12.entry` — `definitional`; author 0, predecessor 2, framework 0, outputs 1, manual obligations 0.
- `CT12.decide.saturation` — `verifiedComputation`; author 0, predecessor 2, framework 0, outputs 2, manual obligations 0.
- `CT12.compute.peel` — `verifiedComputation`; author 1, predecessor 1, framework 0, outputs 1, manual obligations 0.
- `CT12.compute.restoration` — `verifiedComputation`; author 1, predecessor 1, framework 1, outputs 2, manual obligations 0.
- `CT12.verify.decrease` — `genericTheorem`; author 0, predecessor 4, framework 0, outputs 2, manual obligations 0.
- `CT12.terminal.certificate.exhausted` — `genericTheorem`; author 0, predecessor 1, framework 1, outputs 1, manual obligations 0.
- `CT12.terminal.residual.demand` — `genericTheorem`; author 0, predecessor 1, framework 1, outputs 1, manual obligations 0.
- `CT12.terminal.residual.tier` — `genericTheorem`; author 0, predecessor 1, framework 1, outputs 1, manual obligations 0.

### CT13

- `CT13.entry` — `definitional`; author 0, predecessor 1, framework 0, outputs 1, manual obligations 0.
- `CT13.search.tier-one` — `finiteSearch`; author 3, predecessor 1, framework 1, outputs 3, manual obligations 0.
- `CT13.compute.fallback` — `verifiedComputation`; author 3, predecessor 1, framework 2, outputs 1, manual obligations 0.
- `CT13.compute.reconciliation` — `finiteSearch`; author 4, predecessor 1, framework 1, outputs 3, manual obligations 0.
- `CT13.decide.comparison` — `verifiedComputation`; author 1, predecessor 1, framework 0, outputs 3, manual obligations 0.
- `CT13.terminal.residual.tier-one` — `genericTheorem`; author 0, predecessor 1, framework 1, outputs 1, manual obligations 0.
- `CT13.terminal.residual.overlap` — `genericTheorem`; author 0, predecessor 1, framework 1, outputs 1, manual obligations 0.
- `CT13.terminal.residual.deficit` — `genericTheorem`; author 0, predecessor 1, framework 1, outputs 1, manual obligations 0.
- `CT13.terminal.certificate.reconciled` — `genericTheorem`; author 0, predecessor 1, framework 1, outputs 1, manual obligations 0.

### CT14

- `CT14.entry` — `definitional`; author 0, predecessor 1, framework 0, outputs 1, manual obligations 0.
- `CT14.compute.lower-mass` — `verifiedComputation`; author 2, predecessor 1, framework 0, outputs 1, manual obligations 0.
- `CT14.search.members` — `finiteSearch`; author 3, predecessor 1, framework 1, outputs 4, manual obligations 0.
- `CT14.compute.upper-capacity` — `verifiedComputation`; author 4, predecessor 1, framework 0, outputs 1, manual obligations 0.
- `CT14.decide.comparison` — `verifiedComputation`; author 0, predecessor 1, framework 0, outputs 3, manual obligations 0.
- `CT14.terminal.residual.unbounded-member` — `genericTheorem`; author 0, predecessor 1, framework 1, outputs 1, manual obligations 0.
- `CT14.terminal.residual.missing-label` — `genericTheorem`; author 0, predecessor 1, framework 1, outputs 1, manual obligations 0.
- `CT14.terminal.certificate.aggregate` — `genericTheorem`; author 0, predecessor 1, framework 1, outputs 1, manual obligations 0.
- `CT14.terminal.residual.capacity` — `genericTheorem`; author 0, predecessor 1, framework 1, outputs 1, manual obligations 0.

### CT15

- `CT15.entry` — `definitional`; author 0, predecessor 1, framework 0, outputs 1, manual obligations 0.
- `CT15.compute.targetRelativeRank` — `verifiedComputation`; author 3, predecessor 1, framework 1, outputs 1, manual obligations 0.
- `CT15.search.firstRankDrop` — `finiteSearch`; author 3, predecessor 1, framework 3, outputs 3, manual obligations 0.
- `CT15.compute.fullRankLedger` — `verifiedComputation`; author 1, predecessor 1, framework 2, outputs 1, manual obligations 0.
- `CT15.decide.ledgerCapacity` — `verifiedComputation`; author 1, predecessor 1, framework 2, outputs 3, manual obligations 0.
- `CT15.terminal.rankDrop` — `genericTheorem`; author 0, predecessor 1, framework 1, outputs 1, manual obligations 0.
- `CT15.terminal.c4` — `genericTheorem`; author 0, predecessor 1, framework 1, outputs 1, manual obligations 0.
- `CT15.terminal.fullRankLedger` — `genericTheorem`; author 0, predecessor 1, framework 1, outputs 1, manual obligations 0.

### CT16

- `CT16.entry` — `definitional`; author 0, predecessor 1, framework 0, outputs 1, manual obligations 0.
- `CT16.search.support` — `finiteSearch`; author 3, predecessor 1, framework 1, outputs 3, manual obligations 0.
- `CT16.compute.closed-code` — `verifiedComputation`; author 1, predecessor 1, framework 0, outputs 1, manual obligations 0.
- `CT16.decide.closed-code` — `verifiedComputation`; author 2, predecessor 1, framework 0, outputs 3, manual obligations 0.
- `CT16.terminal.residual.proper-support` — `genericTheorem`; author 0, predecessor 1, framework 1, outputs 1, manual obligations 0.
- `CT16.terminal.certificate.exact-code` — `genericTheorem`; author 0, predecessor 1, framework 1, outputs 1, manual obligations 0.
- `CT16.terminal.residual.closed-type-mismatch` — `genericTheorem`; author 0, predecessor 1, framework 1, outputs 1, manual obligations 0.

### CT17

- `CT17.entry` — `definitional`; author 0, predecessor 1, framework 0, outputs 1, manual obligations 0.
- `CT17.search.compatibility` — `finiteSearch`; author 4, predecessor 1, framework 2, outputs 3, manual obligations 0.
- `CT17.decide.scale` — `verifiedComputation`; author 1, predecessor 2, framework 1, outputs 3, manual obligations 0.
- `CT17.enumerate.survivors` — `finiteSearch`; author 6, predecessor 1, framework 2, outputs 3, manual obligations 0.
- `CT17.decide.arithmetic` — `finiteSearch`; author 5, predecessor 1, framework 2, outputs 3, manual obligations 0.
- `CT17.terminal.residual.incompatibility` — `genericTheorem`; author 0, predecessor 1, framework 1, outputs 1, manual obligations 0.
- `CT17.terminal.certificate.exhausted` — `genericTheorem`; author 0, predecessor 1, framework 1, outputs 1, manual obligations 0.
- `CT17.terminal.residual.survivors` — `genericTheorem`; author 0, predecessor 1, framework 1, outputs 1, manual obligations 0.
- `CT17.terminal.certificate.target-hit` — `genericTheorem`; author 0, predecessor 1, framework 1, outputs 1, manual obligations 0.
- `CT17.terminal.residual.orbit` — `genericTheorem`; author 0, predecessor 1, framework 1, outputs 1, manual obligations 0.

## Transition-profile authoring boundaries

| Profile | Family | Semantic discovery | Problem-specific inputs | Adapter type |
|---|---|---|---|---|
| `CT1.residual.avoiding->CT2` | `CT1->CT2` | `capabilityDiscovery` | targetCapability, minimalityKernel | `—` |
| `CT1.residual.avoiding->CT2.localDeletion` | `CT1->CT2` | `capabilityDiscovery` | targetCapability, minimalityKernel | `—` |
| `CT1.terminal.c1->CT12` | `CT1->CT12` | `problemSemanticAdapter` | targetCapability, semanticDiscoveryAdapter | `StructuralExhaustion.Routes.CT1ToCT12.SemanticAdapter` |
| `CT2.residual.separatingContext->CT3` | `CT2->CT3` | `problemSemanticAdapter` | targetCapability, semanticDiscoveryAdapter | `StructuralExhaustion.Routes.CT2ToCT3.PieceDiscovery` |
| `CT2.residual.criticality->CT10` | `CT2->CT10` | `problemSemanticAdapter` | targetCapability, semanticDiscoveryAdapter | `StructuralExhaustion.Routes.CT2ToCT10.DataDiscovery` |
| `CT5.residual.chargeLedger->CT14` | `CT5->CT14` | `capabilityDiscovery` | targetCapability | `—` |
| `CT6.residual.activeLedger->CT9` | `CT6->CT9` | `problemSemanticAdapter` | targetCapability, semanticDiscoveryAdapter | `StructuralExhaustion.Routes.CT6ToCT9.ItemCollectionAdapter` |
| `CT9.residual.overload->CT7` | `CT9->CT7` | `problemSemanticAdapter` | targetCapability, semanticDiscoveryAdapter | `StructuralExhaustion.Routes.CT9ToCT7.ObjectAdapter` |
| `CT14.residual.capacity->CT14` | `CT14->CT14` | `capabilityDiscovery` | targetCapability | `—` |
| `CT1.residual.accumulatedLedger->CT9` | `CT1->CT9` | `problemSemanticAdapter` | targetCapability, semanticDiscoveryAdapter | `StructuralExhaustion.Routes.Accumulated.Adapter` |
| `CT1.residual.accumulatedLedger->CT10` | `CT1->CT10` | `problemSemanticAdapter` | targetCapability, semanticDiscoveryAdapter | `StructuralExhaustion.Routes.Accumulated.Adapter` |
| `CT2.residual.accumulatedLedger->CT1` | `CT2->CT1` | `problemSemanticAdapter` | targetCapability, semanticDiscoveryAdapter | `StructuralExhaustion.Routes.Accumulated.Adapter` |
| `CT3.residual.accumulatedLedger->CT1` | `CT3->CT1` | `problemSemanticAdapter` | targetCapability, semanticDiscoveryAdapter | `StructuralExhaustion.Routes.Accumulated.Adapter` |
| `CT5.residual.accumulatedLedger->CT2` | `CT5->CT2` | `problemSemanticAdapter` | targetCapability, semanticDiscoveryAdapter | `StructuralExhaustion.Routes.Accumulated.Adapter` |
| `CT7.residual.accumulatedLedger->CT5` | `CT7->CT5` | `problemSemanticAdapter` | targetCapability, semanticDiscoveryAdapter | `StructuralExhaustion.Routes.Accumulated.Adapter` |
| `CT5.residual.accumulatedLedger->CT10` | `CT5->CT10` | `problemSemanticAdapter` | targetCapability, semanticDiscoveryAdapter | `StructuralExhaustion.Routes.Accumulated.Adapter` |
| `CT9.residual.accumulatedLedger->CT1` | `CT9->CT1` | `problemSemanticAdapter` | targetCapability, semanticDiscoveryAdapter | `StructuralExhaustion.Routes.Accumulated.Adapter` |
| `CT9.residual.accumulatedLedger->CT5` | `CT9->CT5` | `problemSemanticAdapter` | targetCapability, semanticDiscoveryAdapter | `StructuralExhaustion.Routes.Accumulated.Adapter` |
| `CT9.residual.accumulatedLedger->CT10` | `CT9->CT10` | `problemSemanticAdapter` | targetCapability, semanticDiscoveryAdapter | `StructuralExhaustion.Routes.Accumulated.Adapter` |
| `CT9.residual.accumulatedLedger->CT14` | `CT9->CT14` | `problemSemanticAdapter` | targetCapability, semanticDiscoveryAdapter | `StructuralExhaustion.Routes.Accumulated.Adapter` |
| `CT10.residual.accumulatedLedger->CT5` | `CT10->CT5` | `problemSemanticAdapter` | targetCapability, semanticDiscoveryAdapter | `StructuralExhaustion.Routes.Accumulated.Adapter` |
| `CT10.residual.accumulatedLedger->CT6` | `CT10->CT6` | `problemSemanticAdapter` | targetCapability, semanticDiscoveryAdapter | `StructuralExhaustion.Routes.Accumulated.Adapter` |
| `CT10.residual.accumulatedLedger->CT9` | `CT10->CT9` | `problemSemanticAdapter` | targetCapability, semanticDiscoveryAdapter | `StructuralExhaustion.Routes.Accumulated.Adapter` |
| `CT10.residual.accumulatedLedger->CT14` | `CT10->CT14` | `problemSemanticAdapter` | targetCapability, semanticDiscoveryAdapter | `StructuralExhaustion.Routes.Accumulated.Adapter` |
| `CT12.residual.accumulatedLedger->CT10` | `CT12->CT10` | `problemSemanticAdapter` | targetCapability, semanticDiscoveryAdapter | `StructuralExhaustion.Routes.Accumulated.Adapter` |
| `CT12.residual.accumulatedLedger->CT15` | `CT12->CT15` | `problemSemanticAdapter` | targetCapability, semanticDiscoveryAdapter | `StructuralExhaustion.Routes.Accumulated.Adapter` |
| `CT14.residual.accumulatedLedger->CT1` | `CT14->CT1` | `problemSemanticAdapter` | targetCapability, semanticDiscoveryAdapter | `StructuralExhaustion.Routes.Accumulated.Adapter` |
| `CT14.residual.accumulatedLedger->CT12` | `CT14->CT12` | `problemSemanticAdapter` | targetCapability, semanticDiscoveryAdapter | `StructuralExhaustion.Routes.Accumulated.Adapter` |
| `CT15.residual.accumulatedLedger->CT9` | `CT15->CT9` | `problemSemanticAdapter` | targetCapability, semanticDiscoveryAdapter | `StructuralExhaustion.Routes.Accumulated.Adapter` |
