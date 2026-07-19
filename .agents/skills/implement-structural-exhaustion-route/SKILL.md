---
name: implement-structural-exhaustion-route
description: "Implement or consume a schema-9 executable transition profile between structural-exhaustion CTs. Use for CT1-to-CT2, CT1-to-CT12, CT2-to-CT3, CT2-to-CT10, CT5-to-CT14, CT6-to-CT9, CT9-to-CT7, or CT14-to-CT14 families; semantic discovery adapters; full-ledger preservation; public target execution; transition provenance; and focused transition fixtures."
---

# Implement a Structural Exhaustion Transition

Convert one proved source residual into a public target CT execution through
the single framework-owned executable-transition API. Keep consumer choice out
of tactic capabilities and source residuals.

## Read the schema-9 transition contract

From the repository root, inspect the compiled families and profiles:

```bash
jq '.transitionFamilies[] | {familyId, sourceTacticId, targetTacticId, profiles}' generated/lean-machines.json
jq '.transitionProfiles[] | {profileId, familyId, sourceResidualKind, advanceExecutor, authoringBoundary}' generated/lean-machines.json
```

Read the selected module under `lean/StructuralExhaustion/Routes` and its
matching fixture:

| Transition family | Problem input | Fixture |
|---|---|---|
| CT1 avoidance to CT2 | target capability and `MinimalityKernel` | `Examples/CT1ToCT2AutomationFirst.lean` |
| CT1 avoidance to local-deletion CT2 | `LocalDeletionCapability` and `MinimalityKernel` | `Examples/CT1ToCT2AutomationFirst.lean`, `examples/even_cycle/EvenCycleExample/CT2Audit.lean` |
| CT1 C1 terminal to CT12 | target capability and proof-carrying `SemanticAdapter` | `examples/even_cycle/EvenCycleExample/CT12MaximalMatching.lean` |
| CT2 separating context to CT3 | target capability and `PieceDiscovery` | `Examples/CT2ToCT3AutomationFirst.lean` |
| CT2 criticality to CT10 | target capability and `DataDiscovery` | `Examples/CT2ToCT10AutomationFirst.lean` |
| CT5 charge ledger to CT14 | target capability; no semantic adapter | `Examples/CT5ToCT14AutomationFirst.lean` |
| CT6 active ledger to CT9 | target capability and `ItemCollectionAdapter` | `Examples/CT6ToCT9AutomationFirst.lean` |
| CT9 capacity-one overload to CT7 | target capability, `ObjectAdapter`, and the capacity-one theorem | `Examples/CT9ToCT7AutomationFirst.lean` |
| CT14 capacity ledger to CT14 | independently declared target capability; no semantic adapter | `Examples/CT14ToCT14AutomationFirst.lean` |

Treat the selected profile's source residual kind, target CT, authoring
boundary, and `advanceExecutor` as fixed.

## Enforce the full-ledger edge invariant

Every CT edge consumes
`Core.Routing.ResidualStage sourceTactic Ledger`, where `Ledger` is the entire
accumulated branch ledger. Treat it as the full accumulated ledger. Supply a projection
`current : Ledger → SourceResidual` only to let the profile inspect its current
local residual. Never discard the outer ledger.

Invoke the selected profile's mandatory public `.advance` declaration. It must perform
semantic discovery, target-context and trigger construction, the target
entry's public `execute`, exact predecessor retention, and transition
provenance. Continue only through the returned enabled stage's `.ledgerStage`.
The bare target result may be inspected and used in theorems, but it may never
be chained, seeded as the next stage, or substituted for the accumulated
ledger.

After any ordinary or pointwise transition, consume the returned
`.ledgerStage` literally. Do not rebuild the same type with
`ResidualStage.exact execution`; that discards the operational handoff even
when the equality certificate would make it sound.

For `Routes.Accumulated`, expose output types only through `OutputLedger` and
execute identity-current edges through `advanceCurrent`; reserve `advance` for
a real `Ledger → Source` projection and name that output with
`ProjectedOutputLedger`. Never pass `id` to an application output type. Use
`PointwiseOutputLedger` and
`advancePointwise` for the pointwise analogue. Application code must never
re-expand `transition.onLedger`, `.EnabledStage`, or `pointwiseFamily` merely
to recover these output types. Already selected registered-route families use
`SelectedPointwiseOutputLedger` and `advanceSelectedPointwise`.
Registered specialized profiles that retain their own public executor expose
the enabled type through `Core.Routing.CTTransition.OutputLedger`; `onLedger`
is an internal constructor and must not appear in application code.

When an application node retains the same CT label and adds one theorem or
data value, call `ResidualStage.extend`; its output is a
`LedgerExtension` containing the literal earlier `stage.output` and the new
dependent value. When the manuscript requires one public CT execution for
every local centre, port, or other index, use
`PointwiseExecutableFamily`. It produces a dependent function pointwise and
must not require a `FinEnum`, list, scan, or synthesized index universe. If
every index instead executes a specialized transition profile whose typed
provenance must be retained, use `PointwiseTransitionFamily`, call its
`.advance`, continue through `.ledgerStage`, and inspect local certificates
only through `.localStage`.

The following surfaces are forbidden in framework and application changes:
`TacticInterface`, `RouteRule`, `GeneratedRoute`, compatibility aliases,
manual predecessor/equality fields, and a freshly rewrapped local
residual. Do not recreate any of them under another name.

## Implement only the declared semantic adapter

The problem layer may supply only the mathematical interpretation named by
the profile's `authoringBoundary`:

- `PieceDiscovery` extracts a CT3 piece from a CT2 separating-context residual.
- `DataDiscovery` extracts CT10's local datum collection from CT2 criticality.
- `ItemCollectionAdapter` maps CT6's active ledger to CT9's duplicate-free local items.
- `ObjectAdapter` maps CT9's exact capacity-one pair to CT7 objects.
- `SemanticAdapter` for CT1-to-CT12 supplies an independently defined loop
  seed and proves its relation to the proof-valued C1 output.

Instantiate the target capability independently. Let capability discovery
produce its proof-carrying seed when the profile declares
`capabilityDiscovery`. Do not put target state, a terminal choice, a completed
target result, context transport, or arbitrary closure evidence into an
adapter.

For CT5-to-CT14 and CT14-to-CT14, supply no adapter. The target capability
already owns its member universe. For local-deletion CT2, let
`LocalDeletionCapability.discover` inspect only its declared piece schedule;
use the framework closure theorem for the disabled certificate and do not add
a global target decider.

When `CT1.TargetCertificateEncoding` applies, use
`LocalDeletion.CertificateProfile` or the appropriate
`Graph.MinimumDegreeCycle.StaticInput` profile and invoke its public
transition execution. Do not rebuild that composition in an application.

## Verify execution and locality

For each profile, prove or expose:

- the compiled `profileId` and CT family are exact;
- discovery returns the required seed or its exact impossibility proof;
- the complete incoming ledger is the enabled stage's predecessor;
- the target entry's public execution produced the stored result;
- source evidence needed later remains reachable through the ledger;
- the target terminal, trace, semantics, totality, and local work bound hold;
  and
- continuation begins from `.ledgerStage`.

Adapt only finite data already carried by the current residual or its immediate
local structure. Preserve observable order with `OrderedCollection`. Never
scan an ambient graph, context, subgraph, or state universe while constructing
an adapter.

## Register and display the transition

For a compiled profile, an example workflow link uses
`kind := .registeredTransition` and its exact `transitionProfileId?`. The
canonical registry resolves the profile's `advanceExecutor`; do not duplicate
that declaration in `automationDeclarations`.

If a CT pair is not in `transitionFamilies`, place ordinary theorem
composition behind one reusable Core, CT, or Graph executor that consumes and
returns the complete accumulated ledger. Do not add application-owned CT
transport. Add a new family/profile only when the recurring mathematical
conversion has a stable source residual, semantic adapter boundary, context
preservation, public target execution, and provenance; then register its
mandatory public `.advance` and add a focused fixture before any application
uses it.

## Completion gate

Compile the source CT, transition profile, target CT, and fixture together.
Pin the profile ID, exact predecessor ledger, target terminal, typed trace,
and `.ledgerStage` continuation. Run the architecture linter and verify that
every registered workflow link resolves to the compiled profile's public
`.advance`, while ordinary compositions resolve to their framework executor.
Reject application wrappers, missing automation, or any edge that chains a
bare target result.
