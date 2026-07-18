# Node [153] F5: exact missing `ColdBoundedGerm` producer

## Audited edge

The audited source is the exact surviving `FiniteExactStateCorridor.Outcome`
constructed from `LocalCorridorSurvivor` after same-stage F1 and F4 negatives.
For a repeated state, the structural pair is run through exact F2 and then
exact F3. Only universal F2 and negative F3 remains on the F5 edge.

## What is proved on that edge

- Terminal: the actual component corridor is a path and has support bounded by
  `QCold + 1`; the exact Core terminal equation and the F1/F4 negatives are
  retained.
- Repeated: the actual earlier/current prefix pair has equal structural cut
  state and span at most `QCold`; universal target equality, negative F3, the
  exact Core repetition equation, and the F1/F4 negatives are retained.
- The repeated runner is ordered F2 then F3. An F2 distinction exits at F2 and
  an F3 proper representative closes by the verified compression
  contradiction. No new branch is introduced.

These facts are implemented in
`examples/erdos_64_eg/Erdos64EG/P13WeightedColdRestrictedF5Germ.lean` as
`TerminalF5Support`, `RepeatedF5Support`, and
`terminalSupport_or_repeatedF2_or_repeatedSupport`.

The same module now also proves
`terminalSupport_or_repeatedSupport_of_f2_clear`.  Given the exact local F2
negative on every repeated structural pair, it eliminates the distinction
constructor and returns exactly the terminal support or the repeated support
with universal F2 and negative F3.  This is an original-edge strengthening of
the support handoff, not a new branch.  A focused `#check`/`#print axioms`
audit lives in `P13WeightedColdRestrictedF5GermTests.lean`; it reports only
Lean's standard `propext`, `Classical.choice`, and `Quot.sound` axioms.

## Why this is not yet the downstream bounded germ

The refactored neutral `P13ColdGermLedger.ColdBoundedGerm` requires the
following concrete data, none of which follows merely from a bounded corridor
or equality of the current structural state:

1. a `MinimumDegreeCycleReplacement.ProperAtom` whose source is the chosen
   source representative;
2. an actual same-interface replacement piece;
3. equality of the complete boundary-degree profiles;
4. the exact integer length increment `|E| - |Q|`;
5. a finite local `ContextCode`, its decoder and two Boolean response tables;
6. reflection of both response tables and symbolic coverage of every literal
   compatible outside context.
7. a conditional G3 orientation producer, invoked only after response
   neutrality has proved target completeness.

The terminal outcome currently supplies no atom decomposition, alternative
representative, or response-code table. The repeated outcome supplies the two
literal prefix pieces and universal target equality, but not the canonical
exchange atom, exact response-code reflection/coverage, or conditional G3
orientation promised by the manuscript.

Therefore the repeated pair cannot simply be relabeled as the old downstream
germ. A distinct graph-owned exchange constructor is required: it must build
the manuscript's terminal or canonical repeated-state representative, prove
the neutral atom/replacement and increment fields above, produce the finite
local response code with symbolic coverage, and prove the conditional silent
orientation. This is the exact missing producer; no additional proof-flow
outcome is needed or authorized.

## Specification repair completed

The manuscript definition `def:cold-bounded-germ` describes two bounded
same-interface representatives and their response profile, but does not state
that one is already a strictly smaller proper replacement. The Lean record is
now split in that paper-faithful way. The germ itself records the two
representatives, common boundary profile, increment, and response algebra.
`internalTargetFree`, `internalBaseline`, and `locallySmaller` are no longer
unconditional germ fields. The G3 constructor requests them through
`silentExchangeOfTargetComplete` only after the finite response scan is silent
and has derived target completeness. G1/G2/G3 remain the only outcomes. The
ledger and its terminal/table consumers build.

Node [153] F5 nevertheless remains open until the graph-owned terminal and
canonical repeated-state constructors produce the neutral record and its
local response-code coverage.

## Kernel-checked same-interface obstruction

The exact repeated-state predecessor now exposes a sharper obstruction.  The
normalized cold state repeats, but the actual moving boundary vertex does
not.  The canonical component corridor is a simple path and the repeated
positions are strictly ordered, so

```text
currentAmbientEndpoint repetition.first ≠
  currentAmbientEndpoint repetition.second.
```

This is proved by
`P13WeightedColdRestrictedPrefixPackage.repeated_actual_endpoint_ne` in
`P13WeightedColdRestrictedColdGermFrontier.lean`.  Consequently the two full
prefix pieces currently compared by F2 are not already two representatives
of one literal ambient interface.  Equality of their normalized boundary
roles, capped degrees, and D4--D7 code does not supply the missing ambient
vertex identification or a `ProperAtom.reconstruct` isomorphism.

The precise missing original producer is therefore inside the existing
C153.2-to-F5 construction: before declaring the first-failure exchange, it
must cut out the bounded span between the two repeated positions, classify
and own every incidence leaving its interior, and construct the canonical
same-interface representative and complementary outside context.  In the
terminal case it must analogously construct the second completion strand;
the current terminal payload contains only the one actual corridor.  This is
not an additional proof case or edge.  It is the unimplemented semantic
content of the original sentence asserting that the F5 support “carries two
same-interface representatives.”

The bounded cut and its ownership test are now executable.  The generic
`WalkOrderedSpan.twoBoundaryInput` cuts the exact repeated span, and
`repeatedSpanInput_card_le_QCold_add_one` proves its support has at most
`QCold+1` vertices.  `FiniteTwoBoundaryIncidenceOwnership` then scans only
that support and each internal vertex's declared neighbor row.  Its theorem
`escapingInternalIncidences_eq_nil_iff` proves that the resulting list is
empty exactly when every internal incidence stays in the span.

What remains is not the finite scan but its semantic consumer.  The current
F2/F3 predicates compare full earlier/current prefixes, and F4 tests only the
current endpoint against the previously produced handoff ledger.  None of
them consumes an escaping incidence rooted at an arbitrary internal span
vertex.  Therefore the exact original premise still missing is: every entry
of this local escaping-incidence ledger either yields one of the already
named F2/F3/F4 handoffs on the identical occurrence, or is impossible.  Only
the empty residual may proceed to complementary outside reconstruction.

This missing implication is not supplied by induced-path geometry and
ambient cubicity.  The kernel-checked transfer example
`StructuralExhaustion.Examples.FiniteTwoBoundaryIncidenceOwnership` uses the
induced path `0-3-1` in `K_{3,3}`.  Every ambient vertex has degree three, but
the internal path vertex `3` has the escaping neighbor `2`.  Hence a theorem
deriving an empty escaping ledger from “induced span + cubic vertices” would
be false.  A valid proof must use additional target-specific D4--D7 semantics
to send that literal incidence to a genuine existing F2, F3, or F4 witness;
the current `LocalCorridorSurvivor` fields contain no such implication.

## Target-aware D4--D7 clause audit

The declared signature in `original_erdos_64_proof.tex` does not contain the
missing routing theorem. Its clauses have the following exact scopes:

- D4 records raw curvature values on already selected internal wedges;
- D5 records the named Type-A trace/carrier response data;
- D6 records the named Type-B fan/bridge/handoff data;
- D7 records selected sparse-surplus ports, returns, suppression paths,
  triangles, and sparse-pair responses.

An arbitrary edge leaving an internal vertex of the repeated corridor span is
not, from these definitions alone, a Type-A distinction, a proper smaller
representative, a previously named Type-B/route-8 support hit, or a dyadic
cycle. The F2, F3, and F4 Lean contracts correctly demand those full semantic
witnesses; none can be constructed from adjacency and nonmembership alone.

The power-of-two-aware local example
`Erdos64EG.Internal.P13ColdSpanEscapingIncidenceCounterexample` makes the
remaining logical gap concrete. It has an induced corridor `0-1-2`, cubic
internal vertex `1`, and escaping incidence `1-3`. That incidence returns to
`0` and closes a triangle, and Lean proves `not PowerOfTwoLength 3`. Hence an
escaping incidence does not automatically supply the F1 contradiction either.
The example intentionally does not claim to be a global minimal
counterexample; constructing one would be the theorem being proved. It shows
that the required step must use a further target-specific theorem, not merely
the local hypotheses currently carried by F5.

The exact unproved original implication is therefore:

> For the identical selected cold-corridor occurrence, every internal
> incidence escaping the repeated span constructs either (i) a compatible
> context giving the existing F2 target distinction, (ii) a strictly smaller
> proper response-equivalent representative giving the existing F3 output,
> (iii) membership in an already produced Type-B or route-8 support giving the
> existing F4 output, or (iv) an actual power-of-two cycle.

Neither the declared-coordinate definition nor the proof of
`lem:cold-corridor-first-failure` proves this statement. In particular, the
proof's sentence that the repeated support “carries two same-interface
representatives” assumes the empty residual of precisely this classification.
No new node or edge is needed to repair it, but the theorem itself is new
mathematical content that cannot be replaced by an input assumption.
