# Node [144] obligation ledger

Specification: Part X node `[144]`,
`lem:same-token-bottleneck-routing`,
`thm:homogeneous-overload-geometric-closure`, and
`prop:nonnear-cubic-sharp-overload-routing` in
`proofs/erdos_64_eg/erdos_64_proof.tex`.

Node `[144]` remains yellow. Exactly **6 of 13** obligations are proved.

| Task ID | Original-paper obligation/property | Exact predecessor | Lean evidence | Status | Missing producer |
|---|---|---|---|---|---|
| X-144-01 | Consume the literal overloaded token-role fibre and homogeneous matching/star from `[140]`, `[142]`, or `[143]`. | `[140]`/`[142]`/`[143]` | `CoarseBottleneckClassification`, `SemanticBottleneckPairwiseClauseSource` | proved | -- |
| X-144-02 | Find the first collision among the fixed 49 patterns and 48 coarse codes, retaining two distinct source pairs. | X-144-01 | `coarseBottleneckClassification`, verified collision fields | proved | -- |
| X-144-03 | Retain both literal attachment maps and both canonical rooted germs. | X-144-02 | canonical germ residual and semantic trigger | proved | -- |
| X-144-04 | Exhaustively classify first attachment mismatch or full alignment with one of four rooted-germ shapes. | X-144-03 | `semanticBottleneckClassification`, CT10 five-way totality | proved | -- |
| X-144-05 | On divergent germs retain the exact separator, cubic/high decision, cubic star, or high-center port row. | X-144-04 | local consumer, switch normalization, local projection | proved | -- |
| X-144-06 | Expose the first and pairwise local separator clauses without losing the pending semantic obligation. | X-144-05 | `SemanticBottleneckFirstClause`, `SemanticBottleneckPairwiseClause` | proved | -- |
| X-144-06A | Construct the full `Q_geom` routing label from the literal pair data, prove a graph-independent cardinality, and obtain two pairs with the same boundary-degree fibre, bounded P13 labels, terminal roles, suppression flag, and total role as required by `lem:same-token-bottleneck-routing`. | X-144-01 | `SurplusPatternRoutingObservations.portSupportDegree`, `portSupportDegree_le_three`, `boundaryDegreeProfile`, `windowAttachmentLabel`, and their exact equality theorems | partial | The manuscript's boundary degree has now been corrected to degree inside the three-vertex support `T(p)`, yielding six exact `Fin 4` coordinates and removing the false ambient-degree obstruction. The exact 13-bit label on one supplied window is also local. The remaining task is to identify exactly which bounded declared P13-label entries belong to `Z(pi;t,r)`, enumerate that fixed product together with the role/subtype/suppression fields, and replace the coarse 48-code collision by the full `Q_geom` collision. |
| X-144-07 | Route an attachment mismatch to one of the already named sparse surplus exits using an actual distinguishing context or target-defective quotient. | X-144-06A and X-144-06 mismatch | -- | missing | Current mismatch output is only one asymmetric attachment coordinate; no compatible boundaried context or quotient is constructed. |
| X-144-08 | Route aligned parallel/prefix germs through the paper's target-defect, proper compression, or delocalization alternatives; otherwise prove the fixed cap. | X-144-06 prefix | -- | missing | Requires a boundary-degree-fibre response quotient on the literal germ support and context-universality/replacement routing. |
| X-144-09 | Route a cubic separator through the switch quotient to target defect, compression, or delocalization. | X-144-06 cubic | -- | missing | The cubic-star data and pairwise inequalities exist, but no switch response algebra or compatible-context theorem is produced. |
| X-144-10 | Turn a high separator into the exact decorated Type-B fan handoff, including fan-safety or a named sparse exit for every failure. | X-144-06 high | `rootDivergentPairSurvivor`, `afterEdgeDivergentPairSurvivor`, `classifyRoot`, `classifyAfterEdge`, `assignedOpenPair_fanClosed` | partial | The fixed local table eliminates shared-shoulder and triangular endpoint failures by literal four-cycles; a surviving compatible open pair is converted to its exact assignment frontier, and an actual assigned entry closes both ports.  The predecessor still supplies neither the counted connected remainder core, the two complete connector tails/arms and their terminal coordinates, nor the `FanWindowProfile`/`AssignedPair` and pairwise fan-safety facts.  Open--open endpoint failure likewise has no named sparse-exit certificate. |
| X-144-11 | If sparse exits and decorated Type-B handoffs are absent/routed, derive all three fixed homogeneous caps and the explicit quadratic surplus bound. | X-144-07--10 | `P13NearCubicSpineBound` is the exact output type; node `[138]` and direct node `[19]` constructors are proved. | partial | The overload-side cap theorem is blocked by X-144-07--10. |
| X-144-12 | Return exactly the original node-[144] alternative and pass its near-cubic leaf to the common spine continuation. | X-144-07--11 | `P13Node144NearCubicHandoff` records the exact current predecessor and required spine field. | partial | No constructor is claimed until X-144-07--11 are proved; sparse-exit and Type-B leaves likewise require their actual existing certificates. |

The earliest blocker is X-144-06A.  The original proof invokes the
full-routing-label pigeonhole theorem at this point, whereas the current Lean
predecessor proves only a coarse 48-code collision.  Its bounded-support degree
coordinate is now exact and uniformly finite; the fixed declared P13-entry
schedule and complete product enumeration remain. After X-144-06A, the next
blockers are X-144-07/X-144-08: the local Boolean/shape classification must be
converted into an actual boundaried response quotient and compatible-context
theorem. Pairwise endpoint inequalities alone do not imply any sparse exit,
compression, delocalization, Type-B handoff, or fixed cap.

More precisely, X-144-06A still requires a genuine bounded attachment-label
producer and a uniform cardinality theorem. Enumerating all labels realized in
the current finite graph would yield only a graph-dependent `Q_geom`; the
implementation must enumerate only the fixed entries of the declared support.

All implemented scans remain on the fixed 49-pattern table, the declared
`78 p13` attachment coordinates, or a single supplied local neighbour row.
No ambient graph, context, quotient, path, coloring, or Boolean universe is
enumerated.
