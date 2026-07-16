# Node 184 review: literal local separator projection

## Verdict

Green. Node 184 consumes the exact node 181 normalization and introduces no
new mathematical premise. The implementation is a total projection of each
normalized constructor and reserves node 187 for any stronger semantic
classification.

## Exact residual ledger

- `attachmentMismatch`, `alignedLeftPrefix`, and `alignedRightPrefix` retain
  their exact tag equalities and evidence.
- `cubicRoot` and `cubicAfterEdge` consume the supplied `CubicStar.Data` and
  expose its canonical `SwitchBoundaryShape`, together with equality to the
  canonical projection and exact equality of the four-vertex support.
- `highRoot` and `highAfterEdge` consume the supplied degree lower bound and
  expose `HighCenterPort.ports` at that same centre, its exact cardinality
  equality with the degree, and the inherited lower bound four.

The node does **not** infer sparse exits, response equivalence, CT3 classes,
Type-B structure, fixed capacities, fan safety, or target behavior.

## Ownership and transfer

Reusable content lives in
`Graph/LocalSeparatorProjection.lean`; the surplus-pattern file is only the
typed seven-leaf adapter. The non-Erdős transfer executes the cubic projection
on the existing branching-tree fixture and the high projection on `K5`.

Only the selected centre's declared neighbor order may be materialized. The
visible-work bound is therefore `|V|`; there is no enumeration of universes,
contexts, colorings, or response tables.

## Verification

- `lake build StructuralExhaustion.Graph.SurplusPatternSemanticLocalProjection`
  passed.
- `lake build StructuralExhaustion.Examples.SurplusPatternSemanticLocalProjection`
  passed.
- `lake build Erdos64EG.SemanticBottleneckLocalProjection` passed.
- The scoped source audit found no `sorry`, `admit`, `unsafe`, or new `axiom`.
- `#print axioms` reports only standard Lean axioms for the constructors and
  projection. The official endpoint additionally inherits exactly the sole
  permitted Hegde--Sandeep--Shashank theorem axiom.

## Successor

Node 187 remains white. Any subsequent classifier must consume these literal
local projections and separately prove every stronger semantic interpretation.

## Independent cross-review

An independent dependency-cone audit confirms the green verdict without a
theorem-bearing repair.

- `SemanticBottleneckLocalProjectionSource.node181Exact` equates the source
  with the actual integrated node-181 runner.  The projection structure is
  indexed by that exact dependent source and its `projectionExact` field
  equates the value with the reusable graph projector.
- `project` covers all seven normalized constructors.  Attachment mismatch
  and both prefix leaves retain their exact tag equalities and evidence.  Each
  cubic/high root or after-edge leaf is handled separately; no leaf is merged
  with a sibling or discarded.
- A cubic projection uses the literal `CubicStar.Data` supplied by node 181.
  Its `shape` is definitionally the canonical `switchBoundaryShape`, and
  `supportExact` identifies the center plus the range of its three injective
  boundary labels with the exact four-vertex star support.  Adjacency,
  distinctness, and cubicity are inherited from that data rather than
  recomputed.
- A high projection uses `HighCenterPort.ports` at the identical root or
  separator.  `portsExact` fixes the declared neighbor order,
  `cardExact` proves `ports.card = degree center`, and `atLeastFour` is obtained
  by rewriting that equality with the inherited `4 <= degree center` proof.
- Materializing one high-center neighbor schedule costs at most one adjacency
  decision per declared ambient vertex.  The cubic and pass-through leaves do
  no larger work, so the uniform bound `visibleChecks <= |V|` is valid.  No
  context, response, graph, coloring, or other ambient universe is scanned.
- The non-Erdős transfer executes the canonical cubic projection on the named
  branching tree and the high projection on `K5`, checking the exact support,
  port enumeration, cardinality, and lower bound.
- Focused builds and the trust audit pass.  Node-local declarations use only
  `propext`, `Classical.choice`, and `Quot.sound`; the official prefix endpoint
  inherits exactly the permitted HSS theorem from its predecessors.

The implementation proves no sparse exit, response equality, CT3 quotient,
Type-B structure, fixed capacity, fan safety, target behavior, or closure.
Those remain obligations of the white successor.
