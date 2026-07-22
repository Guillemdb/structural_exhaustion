# EG Node 13: boundary-edge overlap blocks replacement

Status: resolved by normalized Graph replacement contract

Date: 2026-07-21

Affected nodes: historical Node 13 review only

Kernel fixture:
`Hypostructure.Fixtures.GraphBoundaryOverlapCounterexample`

## Immutable Requirement

The sole mathematical authority is `original_erdos_64_proof.tex`.
Definition `def:boundaried-gluing` at lines 5308--5314 identifies equal
boundary labels and takes the union of the two edge sets. Definition
`def:boundary-degree-profile` at lines 5320--5325 records the degree of each
boundary vertex in the local piece.

Lemma `lem:replacement` at lines 5602--5622 assumes, among other clauses, that
the replacement and source have equal local boundary-degree profiles and that
the replacement is locally lexicographically smaller. Line 5619 then infers
that every glued boundary vertex has the same final degree, and line 5621 uses
the local strict decrease to conclude that the glued graph is a smaller
counterexample.

## Failed Implications

Under literal union gluing, either side may own a boundary-to-boundary edge.
For a boundary edge set `E_Y` owned by the outside context, the contribution
of a piece `X` to the glued union depends on `E_X \ E_Y`, not only on the
number of local incidences in `E_X`. Therefore

```text
local boundary degrees of X = local boundary degrees of X'
```

does not imply equality of final glued boundary degrees. For the same reason,
a strict local edge-count decrease can be cancelled when an edge removed from
the replacement was already duplicated by the context.

## Kernel Evidence

`GraphBoundaryOverlapCounterexample.lean` constructs two connected pieces on
the same four-vertex boundary and one unrestricted outside context. The kernel
checks all of the following:

- both pieces have uncapped boundary profile `(3, 4, 3, 1)`;
- the outside context owns boundary edge `0-1`;
- the source also owns `0-1`, while the replacement does not;
- the glued degree at boundary vertex `0` is `3` for the source and `4` for
  the replacement;
- the replacement is locally smaller because `8 < 9` local edges; and
- both glued graphs have exactly `9` edges.

The fixture introduces no authored axiom, `sorry`, `admit`, or `unsafe`
declaration. Its audited theorems use only the standard Mathlib trust
footprint.

## Legacy Evidence

Only after reconstructing the original obligation, the checked legacy module
`lean/StructuralExhaustion/Graph/PackedBoundariedGluing.lean` reveals a
stronger representation: its context structure includes `noBoundaryEdge`, and
its additive gluing edge-count theorem relies on that field. This makes the
legacy replacement argument valid for the normalized context class, but the
normalization premise is not stated in the original definition or Node 13
hypotheses.

The legacy implementation therefore cannot be used as authority to add that
premise silently.

## Generic Repair Space

Any approved repair must make both degree preservation and strict global
progress derivable. Three mathematically plausible contracts are:

1. Normalize every decomposition so the outside context owns no
   boundary-to-boundary edge, and prove that normalization preserves the
   original gluing and all response semantics.
2. Require exact agreement of source/replacement overlap with the actual
   outside context, together with the resulting global progress certificate.
3. Strengthen the immutable boundary profile to record the boundary adjacency
   trace needed for every unrestricted context, rather than degree totals
   alone.

Hypostructure may implement the domain-generic identities and executors needed
by these contracts. The EG application may not select one as an original-paper
fact without explicit approval.

The generic identities are now implemented in
`Hypostructure.Graph.BoundaryOverlap`. They prove exact degree and edge-count
inclusion--exclusion and the two strengthened transfer theorems without
choosing a repair for the EG application.

## Resolution

The corrected Hypostructure translation follows the legacy kernel strategy:
replacement is stated for normalized proper atoms whose outside context owns
no boundary--boundary edge.  Graph packages that condition in
`NormalizedProperBoundariedAtom`, derives the zero-overlap degree and edge
count consequences internally, and runs
`executeFocusedNormalizedAtomReplacementCounted` through Core proof
projection.

Node 13 now records no manual overlap obligation.  The unrestricted-overlap
counterexample remains useful Graph evidence for the broader unrestricted
gluing API, but it no longer blocks the EG normalized replacement node.
