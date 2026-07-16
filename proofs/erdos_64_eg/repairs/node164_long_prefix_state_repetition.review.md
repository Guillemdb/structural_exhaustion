# Node `[164]` implementation review

Status: **PASS as an honest refinement-frontier node**.

This review applies the acceptance contract in
`node164_long_prefix_state_repetition.prereview.md`.  Node `[164]` does not
claim CT8 response equivalence or a removable corridor segment.  It proves an
actual repeated graph-derived coarse label among the first nine literal
prefix entries and routes the missing semantic layer to a typed CT10
classifier.

## Exact predecessor and branch separation

`P13SameWindowLongPrefixStateSource` retains both the exact node-`[163]`
result and an equality with
`runP13SameWindowLongSupportPrefix fork quiet long`.  The public node-`[164]`
runner accepts this dependent source; it does not accept an arbitrary support
length, support list, or `LongFiniteSupportHandoff.Source`.

The implementation imports only node `[163]` plus theorem-independent Graph,
Route, Core, and CT10 infrastructure.  It imports no node `[170]`--`[175]`
application module and consumes no short-branch P13 payload.

## Literal full-prefix provenance

For every `PrefixPosition` in the exact node-`[163]` source,
`p13SameWindowLongPrefixSupportPosition` casts the generic prefix embedding
back to the identical corridor support stored by `quiet`, and
`p13SameWindowLongPrefixVertex` reads that literal list entry.

`P13SameWindowLongPrefixOccurrence` retains:

- the exact prefix and full-support positions;
- the literal corridor vertex;
- its ambient degree modulo four; and
- exact membership in `p13CoveredVertices ctx`.

The full prefix enumeration is duplicate-free, exhaustive, and has exactly
`Qbase + 1` positions.  The executable nine-position schedule embeds
injectively into this full prefix, and
`p13SameWindowLongPrefixObservedVertex_exact` proves that its generic vertex
is the same literal corridor entry.

## Honest finite label and collision

The reusable label is

```text
(ambient degree mod 4, membership in the selected P13 packing).
```

It is graph-derived, non-constant as an operator, exactly enumerable, and has
cardinality eight.  The runner uses `decideWithDecEq` on the first nine actual
ordered prefix entries and retains `decisionExact`, tying its stored collision
to that executable decision.  Therefore it returns two distinct actual prefix
positions with the same coarse label.  The label universe is used only in the
pigeonhole proof and is never materialized by the executable scan.

This stronger eight-label pigeonhole permits the runner to avoid constructing
the approximately 22-million-entry full-prefix list.  It performs at most 36
observed pair comparisons.  Because the equality test does not cache codes,
the visible ledger charges both graph-derived label evaluations per comparison,
including degree and marked-set membership work, and proves

```text
visibleChecks <= 144 * (vertexCount + 1).
```

The retained CT10 classification adds nine conservative class/row checks, so
the complete local bound is

```text
visibleChecks + ct10Checks <= 144 * (vertexCount + 1) + 9.
```

No graph, subset, path, Boolean-function, or ambient state universe occurs in
the runner or work term.

## CT8/CT10 semantic boundary

The coarse repeat is stored in
`Graph.LongPrefixObservedLabel.SemanticRefinementResidual`.  It is not passed
to CT8 because no complete compatible response-context enumeration and no
certified smaller-object transport are available on this long branch.

The typed route retains the exact repeat.  Its CT10 ordered datum collection
is exactly the two distinct occurrence indices returned by that repeat; it is
not a singleton marker or a canned run disconnected from the graph result.
CT10 classifies those retained observations over three ordered semantic
layers:

1. coarse label (present);
2. compatible response contexts (missing);
3. certified removal (not reached).

Both actual observations populate the coarse-label row.  The CT10 result is
proved total and verified, its exact trace is
`entry, table, direct, missing, promotion, promotedTerminal`, its terminal is
`promoted`, and its first promoted obligation is exactly `responseContexts`.
This is the new open frontier; it is not an author-supplied Boolean realization
assumption.

## Transfer, build, and trust audit

The theorem-independent transfer module
`StructuralExhaustion.Examples.LongPrefixObservedLabel` checks the generic
repeat, equal-label, and visible-work theorems for an arbitrary finite graph,
support, and local marked set.

Focused builds passed:

```text
lake build StructuralExhaustion.Graph.LongPrefixObservedLabel
           StructuralExhaustion.Routes.LongPrefixObservedLabel
           StructuralExhaustion.Examples.LongPrefixObservedLabel

lake build Erdos64EG.P13SameWindowLongPrefixStateLabels
```

The four new source files contain no `sorry`, `admit`, or declared axiom.
`#print axioms` for the generic repeat/work theorems, CT10 route theorems, and
node-`[164]` provenance/repeat/work theorems reports only Lean's standard
`propext`, `Classical.choice`, and `Quot.sound`; no new native-decision or
problem-specific axiom is introduced.

Per the assigned integration boundary, this implementation does not edit the
TeX manuscript, web export, test umbrella, package umbrella, or implementation
log.  Those artifacts remain for the coordinating session.  In particular,
the current manuscript wording for node `[164]` still asks for full sound
state-label/repetition semantics.  Green integration must narrow node `[164]`
to this first-nine coarse-repeat/refinement classifier and move the complete
D4--D7/CT8 semantic consumer to a new white downstream node.

## Independent defect history

The initial cross-review found two required corrections.  First, the work
ledger charged one label evaluation per observed pair although the uncached
equality test evaluates two.  Second, the route retained the CT10 result but
did not expose its exact promoted trace or totality.  The repaired files now
retain the exact collision decision, charge both evaluations, include the
nine-check CT10 ledger, and expose CT10 terminal, trace, validity, trace
validity, and totality in both the reusable route/transfer layer and the P13
adapter.  The complete focused build and trust audit was rerun after repair.
