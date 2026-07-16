# Node 180 D4--D7 semantic-readiness cross-review

## Verdict

**PASS**, after strengthening the non-Erdős transfer fixture to audit the
anchor impossibility and all three retained missing-witness projections.

The verified contract is the narrowed semantic-readiness fork, not the old
full CT8 claim.  The latter remains the white successor.

## Local contract audit

| Incoming node-175 constructor | Exact predecessor content | Node-180 check | Verified output |
|---|---|---|---|
| coarse repeat | routed CT10 consumer, exact repeated pair, and both `MissingD4D7Reconstruction` witnesses | inspect the already computed constructor | `D4D7CoarseSemanticBlock`, retaining the routed consumer and both witnesses |
| bounded first missing | bounded ledger, routed CT10 consumer, exact first missing row, and its marker | inspect the already computed constructor | `D4D7BoundedSemanticBlock`, retaining the bounded ledger, routed consumer, and marker |
| bounded reconstructed | a family claiming `D4D7ClausesDerived` for every actual stored stub | apply the family at the stored anchor stub | contradiction, since `D4D7ClausesDerived` has no constructor in the current graph profile |

### Exact provenance

`D4D7SemanticReadinessSource.node175Exact` identifies the supplied predecessor
with `runD4D7OrCoarseRepeat source174 source175`; it is not a restated author
premise.  Node 175 in turn executes
`InducedPathComponentD4D7OrCoarseRepeat.run` on `source175.graphSource`, whose
`node174Exact` identifies its input with the exact generic node-174 run, and
whose `source175.node174Exact` identifies the specialization with the actual
P13 node-174 execution.  Thus node 180 consumes the literal node-175 result on
the identical transition, source-174 ledger, and dependent branch context.

### Impossibility audit

`anchor_mem_stubs` proves membership by unfolding the actual stored schedule,
whose head is `anchorStub input`.  A `ReconstructedFamily` provides a value of
`D4D7ClausesDerived input stub` for every member of that schedule.  Applying it
at the anchor therefore produces an inhabitant of the constructor-free
derivation-status proposition and closes by `nomatch`.  The proof does not
assume absence of a mathematical response; it proves only that the current
graph-owned derivation profile cannot return its complete-family constructor.

### Surviving witnesses and CT10 data

The coarse block retains the entire `D4D7RoutedCoarseRepeat`, not merely the
two markers, so its CT10 execution and exactness theorem remain available.
The bounded block likewise retains `D4D7RoutedFirstMissing` and the bounded
length ledger.  Its `missing` field is exactly `routed.residual.marker` at the
first actual missing row.  No witness is synthesized at node 180.

## Locality, ownership, and transfer

The runner performs one case analysis on the already computed node-175
constructor.  Its visible work is `1 <= localScale + 1`; every row scan and
CT10 check belongs to node 175.  It enumerates no state, response, context,
graph, or ambient universe.

Reusable impossibility and semantic-readiness logic is graph-owned.  The P13
file retains its application-specific routed wrapper types and is a thin
case analysis over the exact specialized node-175 output.  The independent
transfer `Examples.ComponentD4D7SemanticReadiness` now checks:

- exact generic predecessor execution;
- actual anchor membership;
- impossibility of a reconstructed family;
- both coarse missing-witness projections;
- the bounded missing-witness projection;
- exhaustive execution and the local work bound.

## CT8 and trust audit

No CT8 capability, response-context enumeration, response-equivalence proof,
removal operation, or `Core.SmallerObject` is constructed.  Node 180 only
states why those inputs are unavailable and returns typed obstruction blocks.

`#print axioms` on the graph impossibility/exhaustiveness theorems and the two
public P13 endpoints reports only `propext`, `Classical.choice`, and
`Quot.sound`.  There is no HSS dependency, new axiom, `sorry`, `admit`, or
unsafe declaration in the reviewed files.

## Validation

Passed:

- `lake build StructuralExhaustion.Graph.InducedPathComponentD4D7SemanticReadiness StructuralExhaustion.Examples.InducedPathComponentD4D7SemanticReadiness`
- `lake build Erdos64EG.P13SameWindowComponentD4D7SemanticReadiness`
- focused `#print axioms` audit
- `git diff --check` on the review-local transfer edit

Existing warnings replayed from predecessor modules and are unrelated to node
180.  Shared imports, TeX, web crosswalk, counts, and generated files were not
edited during this independent review.
