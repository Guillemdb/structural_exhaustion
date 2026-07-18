# Node [144]: high-compatible canonical-port origin contract

## Manuscript boundary

The high-separator leaf first produces two distinct literal ports at the same
high center.  The local compatibility table can then certify
`FanCompatible`.  This is not yet the Type-B assignment claimed later in the
paper.

The exact consumer is
`lem:compatible-pair-fan-closure` in `original_erdos_64_proof.tex`.  Its
hypothesis is explicitly conditional: **in an assigned Type-B fan-window
profile** the two port endpoints must be remainder-side and the four shoulder
incidences must be assigned.  Only then does the lemma return two fan-closed
ports and four pairwise distinct local carriers.  The corollary
`cor:compatible-pair-typeB-routing` additionally asks that the profile be an
admissible Type-B profile which records the common center.

Consequently the node-[144] high-compatible leaf has two rigorous local
stages.

1. Classify the exact types of the compatible ports.  In the open--open case,
   construct the two `FanClosedPort.OpenPort` values from the recovered raw
   ports, construct the exact `FanClosedPort.CompatiblePair`, and derive the
   four-carrier `Nodup` theorem.  If either port is triangular, retain the
   exact ordered `PairCase` and compatibility proof as a triangular-compatible
   residual; it belongs to the manuscript's separate triangular route.
2. Preserve an open-compatible assignment frontier.  It contains the common
   center, both raw ports, both open proofs, their literal provenance, the
   compatible-pair proof, and the four distinct carriers.  Its consumer must
   supply a graph-owned `FanWindowProfile` and an `AssignedPair`.  From those
   facts the existing fan-closure assembly is valid.

## What node [144] does not currently prove

The detailed separator data do not include the node-[64] localized support,
its connected remainder core, or its induced-core assignment predicate.  In
particular, they prove neither that the two recovered endpoints lie in the
packing remainder nor that the four shoulder incidences are assigned to one
fan envelope.  Reusing `TypeBFanWholePortAssignment` would therefore require a
`VerifiedNode64Residual` that this branch does not possess.

The smallest honest residual is thus not “compatible but unproved.”  It is the
fully proved open-compatible origin together with the precise missing semantic
handoff:

- a canonical Type-B fan-window profile tied to the current packing/remainder
  and actual fan envelope;
- remainder-side proofs for the two literal port endpoints; and
- assignment proofs for the four literal shoulder carriers.

No graph, vertex set, path family, or Boolean universe is enumerated here.
The only executable split is the fixed two-port type table already used by the
high-separator classifier.

## Lean implementation sketch

- `Graph/HighCompatiblePortOrigin.lean`
  - `OpenCompatibleOrigin`: exact raw-port origin, open subtypes,
    `CompatiblePair`, and four-carrier `Nodup`.
  - `TriangularCompatibleResidual`: exact non-open ordered `PairCase` plus the
    unchanged `FanCompatible` proof.
  - `classify`: a four-case split on `classifyPairCase`.
  - `AssignmentFrontier` and `AssignedEntry`: the former is derivable from the
    open-compatible origin; the latter is exactly the manuscript's assigned
    profile premise.
- `Graph/SurplusPatternHighCompatibleOrigin.lean`
  - root and after-edge adapters retaining the complete detailed-separator
    provenance while applying the generic classifier.
- `Erdos64EG/SemanticBottleneckHighCompatibleOrigin.lean`
  - thin exports and local origin/frontier tests; no new Erdős mathematics.

The next mathematical obligation after these bridges is to construct the
canonical assigned profile from the actual node-[144] surplus branch, or to
route that branch to an earlier verified `VerifiedNode64Residual`.  It may not
be replaced by an arbitrary profile whose predicates are defined to be true.
