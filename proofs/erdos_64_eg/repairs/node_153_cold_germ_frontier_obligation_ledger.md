# Node [153] XI-153-12 cold-germ frontier ledger

Authority: `original_erdos_64_proof.tex`, the F5 paragraph of
`lem:cold-corridor-first-failure`.  No node, edge, or proof outcome is added.

## Implemented predecessor obligations

| Obligation | Lean evidence | Status |
|---|---|---|
| Preserve the exact repeated F5 predecessor and its actual earlier/current prefix pair. | `RepeatedColdGermFrontier.support`, `pair`, `pairExact` | proved |
| Preserve equality of the complete normalized structural state. | `RepeatedColdGermFrontier.structuralEqual` | proved |
| Recover equality of capped boundary degrees and active half-edge roles from that same state equality. | `cappedBoundaryDegreeEqual`, `activeHalfEdgeRoleEqual` | proved |
| Preserve the exact span bound `≤ QCold`. | `RepeatedColdGermFrontier.spanBound` | proved |
| Preserve universal response of the two existing full-prefix pieces and the exact F3-negative certificate. | `targetUniversal`, `noProperPrefixRepresentative` | proved |
| Prove the actual moving endpoints of the repeated positions are distinct. | `currentAmbientEndpoint_ne_of_val_lt`, `repeated_actual_endpoint_ne` | proved |
| Preserve the exact terminal path, `QCold+1` support bound, F1 negatives, and F4 negatives. | `TerminalColdGermFrontier`, `terminalColdGermFrontier` | proved |
| Cut the literal induced span between the two repeated positions, with those actual positions as its two boundaries. | generic `WalkOrderedSpan.twoBoundaryInput`; Erdős `repeatedSpanInput` | proved |
| Relate repeated occurrence indices to path positions, including the positive-stage offset. | `repeated_first_val_eq_index_add_one`, `repeated_second_val_eq_index_add_one` | proved |
| Prove the actual stage span is at most `QCold` and its induced support has at most `QCold+1` vertices. | `repeated_stage_span_le_QCold`, `repeatedSpanInput_card_le_QCold_add_one` | proved |
| Enumerate exactly the incidences escaping internal span vertices, scanning only the span support and declared neighbor rows. | `FiniteTwoBoundaryIncidenceOwnership.escapingInternalIncidences`; `repeatedSpanEscapingIncidences` | proved |
| Prove empty escaping ledger is equivalent to complete internal-incidence ownership and expose the local decision. | `escapingInternalIncidences_eq_nil_iff`, `repeatedSpanOwnershipDecidable` | proved |

Delta: **12/12 dependency-ready XI-153-12 predecessor obligations proved**.
The focused test target builds in 8,954 jobs and its axiom audit contains only
`propext`, `Classical.choice`, and `Quot.sound`.

## First non-derivable original obligation

The first missing semantic producer is the original C153.2/F5 assertion that
the bounded support carries **two representatives of one literal interface**.
The current repeated payload carries two full prefixes whose moving ambient
endpoints are provably distinct.  The current terminal payload carries only
one corridor strand.  Neither payload supplies:

1. a proof that the newly computed escaping-incidence ledger is empty, or an
   existing F2/F3/F4 consumer for every nonempty entry;
2. a complementary packed outside context reconstructing the selected graph;
3. a second terminal strand or canonical repeated-state representative on the
   same literal boundary vertices;
4. equality of the full packed boundary-degree profiles; or
5. the finite response table with reflection and symbolic context coverage.

These are the graph-owned semantic contents required to construct
`MinimumDegreeCycleReplacement.ProperAtom` and `ColdBoundedGerm`.  Adding them
as caller hypotheses would merely assume XI-153-12, so no such constructor is
introduced.  The required producer belongs to the existing C153.2-to-F5 edge:
cut the repeated span (or terminal exchange), classify every side incidence
through the existing F2/F3/F4 routes, and only then construct the same-interface
atom, canonical representative, outside reconstruction, and response table.

The current exact F2/F3/F4 APIs do not consume an escaping internal incidence:
F2/F3 compare two full prefix pieces, while F4 recognizes membership of the
current prefix endpoint in an earlier declared support.  They do not prove
that an arbitrary side neighbor of an internal span vertex is absent or
charged.  Thus `LocalCorridorSurvivor` cannot currently prove the ownership
predicate.  This is the first precise remaining premise on the existing edge.

The absence is mathematically substantive, not merely an API omission.  The
non-Erdős `K_{3,3}` transfer test constructs an induced three-vertex path with
all ambient degrees equal to three and a certified escaping incidence from its
internal vertex.  Therefore no bridge from only path inducedness and cubicity
to `RepeatedSpanIncidencesOwned` can be implemented.  The required earlier
premise is a target-specific clause theorem saying that each computed
escaping entry yields the full witness demanded by one existing F2/F3/F4
constructor on the identical occurrence.
