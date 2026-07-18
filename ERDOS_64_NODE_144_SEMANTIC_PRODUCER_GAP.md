# Node [144] semantic producer gap

Authority: `proofs/erdos_64_eg/erdos_64_proof.tex`,
`lem:same-token-bottleneck-routing` and
`thm:homogeneous-overload-geometric-closure`.

This is a gap in the current Lean implementation and in the data supplied to
the corresponding manuscript argument. It is not a missing finite table.
The present node-[144] predecessor computes:

- one first attachment mismatch, or equality of all `78 p13` attachment
  predicates;
- one of the two prefix and two divergent rooted-germ shapes;
- for a divergent shape, its cubic-star or high-degree local incidence data;
- pairwise distinctness of the exposed local endpoints.

Those facts do not construct any of the semantic objects used in the next
paragraph of the paper.

## Earliest missing producer: the full routing label

The original proof of `lem:same-token-bottleneck-routing` starts with more
than `Q_geom` pairs carrying the same full routing label. That label includes
the boundary-degree fibre, bounded `P13` label entries, both terminal roles,
the suppression/free-anchor flag, token subtype, and total role.

The current Lean node-[144] instead starts with exactly 49 pairs and proves a
collision in a 48-valued **coarse** code containing only token subtype,
endpoint role, open/triangular status, and terminal germ role. The repository
contains no complete `Q_geom` finite type or cardinality theorem. The
boundary-degree coordinate itself is now repaired: it is the exact degree
inside the three-vertex support `T(p)`, hence an exact `Fin 4` value, rather
than the previously mistranslated ambient degree.
Consequently the first sentence of the original routing proof cannot yet be
instantiated. In particular, the number 49 is not a proved
`Q_geom + 1` threshold.

There are two distinct obligations here, neither of which is discharged by
the sentence “these labels form a finite set” in the source manuscript:

1. **Exact producer.**  The current routed pair data contains the two literal
   three-vertex port supports, their open/triangular responses, and the
   selected-window adjacency predicate.  It does not contain a declared
   `P13Label` for every window-label entry said to occur in the bounded
   support.  `CT9FanLabelPacking.MarkedFan.attachment` is caller-supplied data,
   not a theorem extracting such labels from a routed pair, so it cannot fill
   this field without assuming the required producer.
2. **Uniform cardinality.**  The original proof later sets
   `L_geom := Q_geom + 1` and uses it as a fixed homogeneous cap to conclude
   `sigma(G) = O(sqrt n)`.  Finiteness for each fixed finite graph is
   insufficient for that inference. The six degree entries are now uniformly
   finite, but the implementation has not yet extracted the fixed list of
   declared `P13` entries occurring in the bounded routing support. No theorem
   yet packages those entries into one graph-independent full label.

The locally determined part is formalized in
`SurplusPatternRoutingObservations.lean`: `boundaryDegreeProfile` is the
literal six-entry bounded-support degree function with codomain `Fin 4`, and
`windowAttachmentLabel` is the exact thirteen-position `P13` label on one
supplied packed window. Their equality theorems preserve every entry exactly.
This does not enumerate the ambient window family.

Thus replacing the 48-code collision by a product enumeration over the
literal current graph would not repair the proof.  It would only produce a
graph-dependent threshold and would not justify the fixed-cap consequence.
The required repair is an existing-edge producer theorem proving a uniformly
bounded normalization of every listed field (with preservation sufficient for
all later quotient and fan-safety consumers), followed by the exact finite
cardinality calculation.  No such normalization may be inferred by truncating
degrees or forgetting window identities: equality of the normalized code must
be proved to preserve every semantic field used downstream.

## Cross-check against the existing Type-B stratification

The original high/Type-B route does not supply the missing predecessor bound.
`def:marked-typeB-fan` makes a legal pairwise-compatible label map
`S_h : N(h) -> labels` part of an already assigned certificate-marked fan.
Only then does `lem:fan-certificate` prove `d_G(h) <= 8`.  If that assignment
is absent, the manuscript routes `h` as a fan-certificate residual center.
In Lean this order is literal: `CT9FanLabelPacking.MarkedFan.attachment` is a
structure field, `MarkedFan.degree_le_eight` consumes it, and
`TypeBSupportScope.assignedMarkedFan` is optional assigned data.

Therefore this cap cannot be used to construct the earlier full routing-label
collision without circularity: node [144] needs the full collision in order
to produce the decorated Type-B handoff, while the degree-eight theorem starts
only after a marked Type-B fan has already been assigned.  Moreover the cap is
on the fan center, not a proved cap on every boundary-degree entry of the two
port supports.  The non-marked residual route is a downstream Type-B ledger
outcome, not a predecessor state-space bound for `Q_geom`.

## Next missing producer: mismatch and prefix leaves

For the two selected coordinates the proof requires a common finite
boundaried response system with:

1. an actual connected proper atom containing both literal germ supports;
2. one common boundary type and equal boundary-degree profiles;
3. two distinct response coordinates inside that system;
4. a quotient proposal identifying exactly those coordinates;
5. either a concrete compatible context distinguishing their target
   responses, or universal target-response equality;
6. on universal equality, a certified smaller representative/reduction; and
7. if the required support enlargement is proper/global, the exact existing
   delocalization payload.

None is determined by one asymmetric adjacency coordinate or by one rooted
path being a prefix of another. In particular, unequal adjacency to one
packed-window vertex does not by itself imply unequal power-of-two-cycle
response in a compatible outside context.

## Cubic leaf

The cubic-star datum proves three distinct incidences at a degree-three
separator. The paper next identifies two switched coordinates, but the Lean
predecessor contains no switched boundaried pieces, no boundary-profile
equality, no outside response function, and no smaller representative.
The same seven items above must therefore be constructed for the switch
quotient before CT3 or a target-defect route is available.

## High leaf

The high projection supplies an injective port row at one center. To construct
the paper's existing decorated Type-B handoff one still needs:

1. the two separated literal tails with their common center;
2. the open/triangular port-origin assignment;
3. the dyadic two-tail closure check and its sparse-exit consumer;
4. compatible `P13` labels and one boundary-degree fibre;
5. target-response fan-safety or the exact target-defect/compression/
   delocalization route for its failure; and
6. a `RecordedDecoratedHandoff` on the identical support.

The current high-center port row alone does not imply these properties.
The verified local high route does eliminate shared-shoulder and triangular
endpoint failures by literal four-cycles and can expose a compatible pair or
a typed open--open endpoint failure.  Moreover, once an actual assigned entry
is supplied, `assignedOpenPair_fanClosed` proves both recovered ports are
fan-closed.  What remains absent is precisely the producer of that assigned
entry and of the complete decorated-handoff support; importing the unrelated
node-[108] handoff would be cross-branch leakage.

## Consequence

`P13Node144NearCubicHandoff` now records the exact output contract, and the
no-overload node-[138] plus direct bounded node-[19] branches construct the
same `P13NearCubicSpineBound`. No constructor is provided for the overload
side of node [144]. Providing one before the full-label collision and the
objects above exist would assume the theorem that node [144] is required to
prove.

The repair must stay on the existing sparse-exit, Type-B, and near-cubic
outcomes. It must not introduce a residual branch or replace compatible
contexts by an ambient enumeration.
