# Node 195 long-prefix compatible-response frontier review

## Verdict

**READY FOR INDEPENDENT REVIEW.** Node 195 consumes node 192 exactly and
reserves node 198 as the sole semantic successor. It exposes an honest typed
frontier; it does not claim compatible-response equivalence or execute CT8.

## Residual-flow ledger

Node 192 has five dependent leaves. The four local-mismatch leaves pass
through with the identical first-hit and preceding-block alignment payloads.
Each receives exactly two open requirements: deriving a genuine
distinguishing response context from the local mismatch and proving that
context's graph provenance. The first-thirty-six-aligned leaf retains all
four block proofs and receives exactly three open requirements: a compatible
response family, provenance for that response, and either a certified CT8
input or a typed distinguishing-context route.

No leaf is interpreted as stronger semantics. In particular, an adjacency
mismatch at one literal support coordinate is not asserted to be a compatible
gluing context, and agreement on positions 0--35 is not asserted to exhaust
D4--D7 responses.

## Exact provenance

`P13SameWindowLongPrefixCompatibleResponseFrontierSource.node192Exact`
identifies the stored dependent predecessor with the actual node-192 runner.
The graph source uses its exact classification. The nested source still
contains node 179's exact degree execution, while the Erdős result separately
retains node 164's exact CT10 promotion to `responseContexts`; neither is
restated as an assumption.

The theorem
`runP13SameWindowLongPrefixCompatibleResponseFrontier_retains_node192`
reconstructs the predecessor classification from the node-195 output and
proves it equals the exact stored node-192 classification. Thus preservation
of all dependent constructor payloads is checked uniformly, not inferred
from an untyped branch tag.

## Ownership, transfer, and locality

The reusable dependent frontier, requirement ledger, exhaustive runner, and
constant work theorem live in
`Graph.LongPrefixCompatibleResponseFrontier`. The Erdős file is a thin exact
instantiation. `Examples.LongPrefixCompatibleResponseFrontier` executes the
same public runner outside the Erdős package and checks exhaustiveness and the
work ledger.

The node inspects only the already-computed node-192 constructor. It performs
one visible constructor check, exposes at most three obligation tags, accepts
no caller Boolean, and enumerates no response, context, state, graph, path,
coloring, finite-type, or ambient universe.

## Scope

Node 195 defines no response function, response-context enumeration,
compatible-gluing theorem, removal map, `Core.SmallerObject`, CT8 capability,
CT8 execution, or target conclusion. Those graph-derived inputs remain the
work of reserved node 198.

Focused framework, transfer, and Erdős builds pass. Focused `#print axioms`
reports only `propext`, `Classical.choice`, and `Quot.sound`. The scoped scan
finds no `sorry`, `admit`, `unsafe`, new axiom, `Finset.univ`, or `Set.univ`;
diff checks are clean.

Shared imports, WebExport, topology, TeX, README, and implementation-log files
were intentionally not edited because they are concurrently owned.

## Independent cross-review

**PASS; no code repair required.** The dependency-cone audit confirms the
following points.

- `node192Exact` identifies the stored dependent predecessor with the actual
  node-[192] runner on the same `source192`. Its `classification` is used as
  the graph frontier input, and `run_predecessor` reconstructs that exact
  classification from every node-[195] result.
- All five constructors are preserved separately. The first mismatch retains
  its first-hit witness; later mismatch leaves retain every preceding aligned
  block plus the exact mismatch at their own block; the final leaf retains all
  four alignment proofs. No payload is weakened to an untyped tag.
- The nested local source retains `degreeResultExact`, hence node [179]'s exact
  degree-refinement runner. The CT10 statement is inherited through the
  node-192 result from node 164 and asserts only that the exact promoted class
  tag is `SemanticClass.responseContexts`. It does not construct response
  contexts, enumerate them, or prove compatible-response equivalence.
- Each of the four mismatch leaves receives exactly the ordered pair
  `localMismatchToDistinguishingContext` and
  `distinguishingContextProvenance`. The thirty-six-aligned leaf receives
  exactly `compatibleResponseFamily`, `responseProvenance`, and
  `certifiedCT8InputOrDistinguishingContext`. These lists are noduplicated and
  are obligations, not witnesses satisfying themselves.
- Only positions 0--35 from the four existing nine-coordinate blocks are
  retained. There is no fifth block, position 36--44 scan, response/context
  universe, compatible-gluing table, removal map, smaller-object witness, CT8
  capability, or CT8 execution.
- The independent transfer runs the same five-way graph frontier, checks exact
  predecessor retention, exhaustiveness, and the requirement ledger. Visible
  work is one already-computed-constructor inspection; at most three tags are
  emitted.

Focused Graph/example and Erdős builds pass. The scoped source and diff checks
are clean. Trust inspection reports only `propext`, `Classical.choice`, and
`Quot.sound` for the graph and Erdős frontier declarations, including the
nested degree/CT10 provenance theorems; there is no HSS dependency.

Nodes [196] and [198] were not expanded, and no shared integration file was
edited during this independent review.
