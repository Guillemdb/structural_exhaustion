---
name: implement-structural-exhaustion-route
description: Implement a typed route between structural-exhaustion residuals and consumer triggers. Use for CT1-to-CT2, CT2-to-CT3, CT2-to-CT10, or CT6-to-CT9 chains, semantic discovery adapters, context preservation, route provenance, and route execution tests.
---

# Implement a Structural Exhaustion Route

Convert a proved source residual into the smallest consumer seed permitted by a compiled route contract. Keep consumer choice out of tactic capabilities and source residuals.

## Read the live route contract

From the repository root, inspect:

```bash
jq '.routes' generated/lean-machines.json
```

Then read the selected module under `lean/StructuralExhaustion/Routes` and its matching example:

| Route | Problem input | Example |
|---|---|---|
| CT1 avoidance to CT2 | target capability and `MinimalityKernel`; no residual adapter | `Examples/CT1ToCT2AutomationFirst.lean` |
| CT1 avoidance to local-deletion CT2 | `LocalDeletionCapability` and `MinimalityKernel`; no target decider or residual adapter | `Examples/CT1ToCT2AutomationFirst.lean`, `examples/even_cycle/EvenCycleExample/CT2Audit.lean` |
| CT2 separating context to CT3 | target capability and `PieceDiscovery` | `Examples/CT2ToCT3AutomationFirst.lean` |
| CT2 criticality to CT10 | target capability and `DataDiscovery` | `Examples/CT2ToCT10AutomationFirst.lean` |
| CT6 active ledger to CT9 | target capability and `ItemCollectionAdapter` | `Examples/CT6ToCT9AutomationFirst.lean` |

Treat the route's dependent source residual and target context as fixed inputs.

## Implement only semantic discovery

1. Obtain the actual residual from the source execution result. Do not reconstruct an equivalent untyped proposition.
2. Instantiate the consumer capability independently.
3. For a `problemSemanticAdapter` route, define only the declared adapter:
   - `PieceDiscovery` extracts a CT3 piece from a CT2 separating-context residual;
   - `DataDiscovery` extracts CT10's local datum collection from CT2 criticality;
   - `ItemCollectionAdapter` maps CT6's active ledger to CT9's duplicate-free local items.
4. Make enabled discovery return a proof-carrying local seed. Make disabled discovery prove that no seed exists.
5. Let the framework construct the `RouteRule`, target context, trigger, and consumer input.

For the local-deletion CT2 profile, let
`LocalDeletionCapability.discover` scan only its declared piece enumeration.
Use `discover_disabled_of_closure` to turn an enabled deletion-C2
contradiction into the exact disabled certificate; never add a global target
decider merely to use the full CT2 route.

When CT1 is supplied by `CT1.TargetCertificateEncoding`, instantiate
`LocalDeletion.CertificateProfile` with that encoding, the local capability,
and the public-target closure rule.  Its `runAvoiding`, `avoidingSource`,
`targetMinimality`, `routedClosure`, `route`, and `discover_disabled` methods
own the entire composition.  For minimum-degree cycle targets, use
`Graph.MinimumDegreeCycle.StaticInput.certificateDeletionProfile`,
`cycleDeletionProfile`, or `edgeRootedDeletionProfile` instead of rebuilding
the bridge in an application package.

Do not add target tactic state, a selected terminal, a completed consumer result, or arbitrary closure evidence to an adapter.

## Verify the route

For an enabled route, prove or expose:

- discovery returns the expected seed;
- the generated trigger contains exactly the discovered local data;
- the branch context, ambient object, branch state, and baseline proof are preserved;
- source semantic evidence required by the consumer is retained;
- route soundness and stable route provenance hold; and
- the consumer reference runner accepts the generated input.

For a disabled route, prove discovery is disabled and that route generation produces no trigger.

## Preserve locality

- Adapt only the finite data already carried by the residual or selected from its immediate local structure.
- Do not scan an ambient graph universe while routing.
- Keep an observable item order explicit with `OrderedCollection`; do not smuggle duplicates into CT9.
- If extraction requires a reusable mathematical theorem, place that theorem in the graph or core layer and leave the adapter as a thin projection.

## Unsupported CT sequences

Use direct theorem composition when no compiled route exists. Add a new framework route only when a recurring residual-to-trigger relationship has a stable semantic adapter, dependent context preservation, soundness, and provenance. Register it in the canonical registry and update its automation contract before using it as a route.

## Completion gate

Compile the source CT, route, and consumer CT together. Pin the generated route identifier, preserved context, consumer terminal, and typed trace in a small fixture. Run the architecture linter so no producer imports its consumer and no application injects route-owned outputs.
