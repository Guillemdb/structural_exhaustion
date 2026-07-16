# Node 22--24 multi-scale state repair audit

Verdict: **FAIL** for the entropy/density conclusion; **PASS** for the bounded
graph-owned connector classifier implemented in
`P13MultiScaleConnectorState.lean`.

## 2026-07-16 same-context routing and node-24 interface re-audit

The exact valid alternative route is now explicit in
`P13Node21PartXIRoute.lean`.  It maps every member of node `[21]`'s retained
CT12 packing to the already verified thirteen-bit cold fork and its computed
node-`[159]` structural frontier.  The four surplus/dyadic/corridor-high/quiet
subledgers partition exactly `p13 ctx` entries.  This is a local scan of the
supplied packing list and fixed thirteen-bit classifier, not an enumeration of
graphs, completions, supports, or contexts.

This route does not identify actual-adjacency responses with the 91 barrier
responses.  It therefore makes the Part-XI handoff total without making nodes
`[22]` or `[23]` green.

The node-`[24]` type boundary was also too weak: its former `coverage` field
could use the tautological ceiling `windowCeiling := p13 ctx`, so the only
nontrivial field was the downstream strict-quarter budget.  The repaired
`P13WindowDensityStructuralTheorem` now additionally requires the exact
cross-multiplied finite cap

```text
118108581006 * windowCeiling <= 1500000000 * |V(G)|,
```

which is the integer form of the printed window-only comparison
`theta <= 1.5 / 118.108581006`.  Thus an eventual inhabitant must prove the
named density theorem itself and cannot pass merely by supplying a convenient
Part-IV budget hypothesis.

The first unresolved aggregate theorem is a graph-owned bounded-multiplicity
charge/terminal ledger for every non-dyadic node-`[159]` entry.  Its current
local semantic leaves are node `[164]` (long-prefix state/repetition), node
`[172]` (repeated-owner/second connector), and node `[175]` (D4--D7
reconstruction or coarse-repeat consumption).  Node `[174]` is verified, but
its repeated branch still retains two `MissingD4D7Reconstruction` witnesses
and its bounded branch controls only one component schedule.  No current
theorem converts those outputs into the finite density cap or quarter budget.

## Defect freeze

- Stable node: the transition from node 21's 91 finite barrier tables to the
  independent multi-scale window package used at nodes 22--24.
- Failed implication: from separate safe/flat counts for each barrier index,
  infer one admissible completion state for every Boolean assignment to all
  barrier/scale coordinates.
- Smallest verified ancestor: `VerifiedP13MultiScaleCurvaturePrefix`, which
  retains the selected CT12 packing and proves the 91 compatibility tables,
  count audits, and exact product inequality.
- Facts not present there: a dyadic-scale enumeration, a global completion
  type, a gluing operation, target-response reflection for glued completions,
  simultaneous realization, and cross-window commutation.
- The source manuscript was not edited.

## Quantifier normalization

Node 21 proves separate finite statements of the form

```text
for every barrier i, safeCount(i), flatCount(i), and their audited relation.
```

The entropy theorem needs

```text
for every assignment f : Coordinate -> Bool,
there exists one admissible global completion s such that
for every coordinate i, response(s,i) = f(i).
```

The former does not imply the latter.  Even coordinatewise realization

```text
for every i and bit b, there exists s(i,b) with response(s(i,b),i)=b
```

does not produce one simultaneous completion.  The two-coordinate state set
`{00,11}` is the minimal countermodel: both coordinates individually take both
values, while assignments `01` and `10` are absent.

## Implemented local invariant and both-sides test

For each selected window and each of the 91 barrier indices, the repair now
enumerates `n^15` literal ambient vertex sequences.  A valid sequence is an
actual simple outside path of length `a+b <= 14`; its endpoint and middle
attachment labels are actual graph labels, are table-legal, and satisfy the
two local-safe relations.  Its Boolean response is exactly the composed
`C_(a+b)` flat relation.

The exhaustive first-failure classifier returns exactly one of:

1. `complete`: every barrier has an actual locally-safe connector sequence;
2. `missing`: the first audited barrier with a proof that no such sequence
   exists.

The scan bound is `91 * n^15`.  It enumerates neither walks of unbounded
length nor a family of ambient graphs.

This passes the local both-sides test only as a classification step.  The
negative side provides a deterministic bounded first-failure payload.  The
positive side supplies coordinatewise connector presence.  Neither side yet
closes nodes 22--24:

- the missing-connector payload has no proved existing CT consumer trigger;
- connector presence does not imply both flat truth values, a dyadic scale
  family, or simultaneous mutable completions.

Consequently the payload must not be promoted to a density theorem or treated
as a new hypothesis.

The literal cycle bridge now sharpens this failure.  For every valid actual
connector state, `p13BarrierConnectorFlat_true` proves that its composed flat
bit is `true`: a false bit would close the connector path through the selected
window to a forbidden power-of-two cycle.  Hence any response system whose
states are actual connector paths in the fixed target-avoiding graph omits the
constant-false Boolean assignment.  Such a system is unconditionally cold and
cannot pay the hot entropy account.  This is a proof that the fixed-graph
connector invariant is the wrong state universe for the manuscript's intended
hypothetical-completion comparison, not a premise to be requested later.

## Graph-owned selected-window corridor entry

The earliest independent cold-side producer has also been implemented without
assuming `P13LocalBooleanData`, an external stub, a germ, or context coverage.
For every literal CT12-selected window,
`P13SelectedWindowCorridor.routeSelectedWindowCorridor` computes exactly one
of the following outcomes from the ambient graph:

1. the first window position of degree strictly greater than three, which is
   an actual surplus handoff; or
2. if all thirteen positions have degree three, the first external incidence
   in the repository's exact token order, packaged as a literal `CubicStub`,
   followed by the existing bridgeless return-corridor first-failure scan.

The generic selection layer proves that an ambient-cubic window has a token
from the exact fifteen-stub count.  The Erdos instantiation derives the
pointwise degree-three lower bound from the minimal-counterexample baseline.
Thus this entry route is exhaustive and unconditional.

This route does not identify the multi-scale connector classifier's missing
barrier with a cold germ: no such implication has been proved.  It instead
bypasses that invalid connection and starts the cold analysis directly from
every selected graph window.

## Exact remaining semantic bridge

The first absent object is a graph-derived finite type of admissible global
completions at the declared separated dyadic scales.  A valid producer must
also prove:

1. every completion has one response bit for each barrier/scale coordinate;
2. each response reflects the corresponding edge-rooted target test;
3. local changes preserve admissibility and all untouched coordinates;
4. every Boolean assignment is realized, or the first missing assignment is
   routed as a bounded structural residual;
5. products across CT12-disjoint windows are realized by one commuting gluing
   operation, not by a dependent function of unrelated local choices.

`P13CoordinatewiseFlatRealization` intentionally names only the weaker
dependent product-choice statement and is not a completion/gluing contract.

On the cold route, the quiet `ColdStructuralGerm` is now split directly from
the graph-produced corridor at every explicit threshold.  The short side is
an exact `BoundedSameInterfaceResidual`: it retains the literal two-endpoint
source path, its path proof, the quiet germ, and the checked support bound.  It
does not pretend that a distinct smaller replacement or response theorem has
already been found.

The long side now executes CT17 rather than stopping at a generic handoff.
Its finite targets are exactly the bounded exponents in
`PowerOfTwoLength (rootCycle.length)`, its sole offset is literal, its
positions are the corridor support positions, and its value is the actual
restored root-cycle length.  The graph-proved strict scale inequality forces
CT17's arithmetic branch.  A target-hit certificate would be precisely the
power-of-two fact rejected by the quiet germ, so the verified execution ends
in CT17's orbit residual.

The short side now runs CT3 on a practical canonical path-length universe.
Candidates are exactly the positive lengths strictly shorter than the
retained corridor; no ambient subgraph universe is generated.  Coordinates
are all possible simple return lengths below the ambient finite-vertex bound.
The response bit is the exact `PowerOfTwoLength` test on the sum of the path
and return lengths.  Its reflection theorem is proved for every literal
simple return walk.  The complete schedule uses at most
`8 * (n + 1)^2` primitive checks.

Compression and exact-known-row terminals both produce a connected canonical
two-terminal path graph with positive length, strict length decrease, and
response equivalence for every actual simple return.  The remaining CT3
terminals retain their concrete distinguishing or novel-row residuals.  This
runner is indexed by the exact `BoundedSameInterfaceResidual`; the caller
supplies neither candidates, response bits, nor an outcome.

The first remaining obligation is the lift from this certified local
root-cycle replacement to literal packed-graph replacement: reconstruct the
two-boundary gluing, prove the boundary-degree/baseline conditions, and show
that cycles not using the replaced path are unchanged.  Until that theorem is
proved, the local response certificate must not be called a whole-graph rank
drop or minimality contradiction.

## Checks

- `lake build Erdos64EG.P13ActualAttachmentResponse`
- `lake build Erdos64EG.P13MultiScaleConnectorState`
- `lake build Erdos64EG.P13SelectedWindowCorridor`
- `lake build Erdos64EG.P13SelectedWindowGermScale`
- `lake build Erdos64EG.P13ShortPathCT3`
- `lake build StructuralExhaustion.Examples.FiniteConnectorSequence`
- `lake build StructuralExhaustion`
- `lake build Erdos64EG`

All three targets build without `sorry`, `admit`, or new axioms.

## 2026-07-16 F2--F5 constructive re-audit

The printed F2--F5 cold-corridor argument is not an unconditional producer of
node 24 and must not be used to turn nodes 22--24 green.  The exact failures
are structural, rather than missing arithmetic:

1. The hot/cold mass inequality is already downstream of the open 91-bit
   realization and commuting-gluing interface, so the cold calculation cannot
   replace that interface without circularity.
2. Repetition of the current coarse two-boundary state does not retain ambient
   boundary identities or the D4--D7 response coordinates.  Node 174 therefore
   returns `MissingD4D7Reconstruction` honestly; equality of its D1--D3 rows is
   not all-context target equivalence.
3. An F2 target distinction is only a typed target-defect residual.  No current
   theorem turns an arbitrary such residual into a sparse exit or an exit-(4)
   load with a proved charge update.
4. F3/G3 requires an actual reconstructed replacement, internal target
   freedom, baseline preservation, strict lexicographic decrease, and target
   completeness for every compatible context.  None follows from equality of
   a coarse state or from a neutral table row.
5. The equal-length table step incorrectly infers a strictly smaller
   representative merely from removal of a declared coordinate.  Admissibility
   does not construct such a representative, and equal length supplies no
   strict decrease.
6. The increment congruence assumes that the required number of homogeneous
   copies is realizable in the graph.  Arithmetic existence of an integer `j`
   does not construct `j` copies, and no availability lower bound is proved.
7. The deletion of high-degree and handoff corridors as `o(n)` lacks a proved
   bounded-multiplicity charge.  The later subcubic ball estimate applies only
   after that deletion and therefore cannot justify it.

The first admissible new local theorem is the node-175 reconstruction
dichotomy for an actual repeated pair from node 174: construct literal
two-boundary pieces on the retained graph interfaces and return either a
specific compatible distinguishing context, or a complete CT3 replacement
certificate with strict decrease.  Only after this theorem and the analogous
node-164/node-172 consumers are aggregated by the existing
`FiniteBoundedOverlap`/CT4/CT5 machinery can a cold-family count be compared
with `n`.  The independent hot realization (or a genuinely unconditional
replacement for it) is still required to recover the printed coefficient
`118108581006 / 1500000000`.
