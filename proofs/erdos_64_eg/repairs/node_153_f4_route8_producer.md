# Node [153] F4 route-8 producer audit

## Frozen branch state

The F4 recognizer may inspect only supports emitted earlier on the same branch.
There are currently two kernel-checked event sources:

1. an exit-(7) `TypeBEntryRouting.Exit7Handoff`, consumed by node [66];
2. a `P13Node176.RouteEightExtraction`, whose `routeExact` field proves that
   the local Type-B router returned its `route8` constructor and whose
   `coreExact` field identifies the emitted non-window core.

The Type-A chain currently ends at `TypeANode63Support.VerifiedNode63Residual`.
It has not implemented the saturated-receiver exits [89]--[109], the true
route-8 residual [110], the deficit-carrying collection [111], or its indexed
carrier support [114].  Therefore a node-[63] support is not an F4 route-8
event.

## Both-sides table

| Local result | Ledger action | Consumer |
|---|---|---|
| Actual exit-(7) handoff | Execute node [66] and append the identical decorated envelope | F4 Type-B recognition |
| Actual `.route8` extraction | Append its `nonWindowCore`; retain `routeExact` and `coreExact` | F4 route-8 recognition |
| Node-[63] Type-A support without exit classification | Append nothing | nodes [89]--[111] producer frontier |

Thus failure to obtain a route-8 event is positive typed information, not an
empty support and not permission to relabel the Type-A support.

## Lean contracts

- `Core.FiniteProducedSupportLedger.Ledger.sum` combines two exact event
  sequences without manufacturing an event.
- `P13ProducedPriorSupportLedger.node66AndRecord` executes the existing
  Type-B consumer and records the same handoff.
- `P13ProducedPriorSupportLedger.recordRouteEight` accepts only a
  proof-carrying `RecordedRouteEightExtraction`.
- `P13ProducedPriorSupportLedger.TypeARouteEightFrontier` retains the exact
  node-[63] predecessor and lists the four missing producer stages.

The scans are linear in the number of recorded producer events.  They do not
enumerate vertices, supports, contexts, or graphs.

## Branch table

| Branch | Output |
|---|---|
| Type-B event meets the cold endpoint | named Type-B F4 handoff |
| route-8 event meets the cold endpoint | named route-8 F4 handoff |
| neither event meets the endpoint | continue F5 after F1--F4 are negative |
| Type-A classification not yet executed | typed producer residual to [89]--[111] |

Every emitted event has a unique consumer at F4.  The open Type-A residual is
not merged into the cold runner until its producer nodes are implemented.
