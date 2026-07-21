# Node 54 small-edge kernel obligation

The `[52] -> [54]` edge is locally complete in
`examples/erdos_64_eg/Erdos64EG/Node54.lean`: node 52 proves its exact
normalized joint budget, and node 54 proves that the exact strict reverse is
impossible.

The remaining `[53] --yes--> [54]` edge requires the following theorem on the
literal active residual:

```text
node53ForcedPower active
  <= node53FlatPower active * active.output.stateCount
```

Together with `Node50Low`, Core's
`ConditionalFibreProductCost.CertifiedCarrierOutput.forced_pow_lt_flat_pow_mul_upper`
then gives `Node53Large`, contradicting the exact `Node53Small` constructor.
This arithmetic transport is already framework-owned and needs no new route.

The current accumulated ledger does not yet contain the displayed input.
Node 31 stores `node31ConditionalFibreRankProfile`, whose full outcome would
produce it through
`ConditionalFibreRank.Profile.fullOutputOfRankEq`.  Node 32, however, proves
full rank for the different profile
`p13CurvatureFunctionalRankProfile`: its proposition is quotient-code
injectivity on support-stratified determination candidates.  The conditional
fibre profile instead filters the exact realized remainder-state carrier and
requires every sequential safe/flat fibre inequality plus terminal
nonemptiness.  These profiles have different state, rank, and survival
predicates, and no theorem in the current graph layer transports the former
full-rank equality to the latter.

Terminal-fibre emptiness is no longer part of this obstruction.  Core now
provides `ofLedgerWithAcceptedWitness` and transports any distinguished
realization through `SequentialCompatibleExtensionLedger.finalWitness`.
The Erdős ledger carries the original target-avoiding completion, proves that
its cached remainder projection is exact, and proves membership in the one
realized remainder carrier.  Thus, once the graph response theorem establishes
that this realization is accepted by the authored curvature schedule, Core
derives final-fibre nonemptiness automatically.

The remaining mathematical interface is solely the per-coordinate conditional
count

```text
543958 * nextFibre.length <= 111286 * currentFibre.length.
```

The paper's node-32 full-rank statement is presently formalized as injectivity
of quotient codes (equivalently, Boolean target-response independence).  That
proposition alone does not imply the displayed `543958/111286` fibre ratio;
the graph specialization still needs the paper-intended local-choice
realization/regluing theorem on this same residual.  A failure of that theorem
must be shown to produce the already existing node-32 rank-drop constructor;
it must not create a new diagram edge.

The complete `Node54Stage` and its framework terminalizer are now declared,
but the small-budget terminal does not elaborate because the required
`forcedPowerFit` producer is absent. Completing the edge requires a
graph-semantic producer, at the earliest existing rank/curvature node, proving
the conditional-fibre full certificate on this exact accumulated residual (or
soundly mapping its failure to the already existing node-32 rank-drop edge).
It cannot be replaced by a caller input, axiom, status type, or a new diagram
branch.

## Contrapositive audit

The tempting bridge

```text
failed safe/flat prefix ratio
  -> functional target-dependence
  -> node-[32] rank drop
```

is not valid for the rank notion currently defined by the original paper.
The first implication confuses multiplicity with determination. A coordinate
may realize both Boolean target values (and hence be independent of the empty
prefix) while the two fibres have arbitrary positive multiplicities. Nothing
in functional quotient-code injectivity constrains their ratio.

This failure is kernel-checked in
`examples/erdos_64_eg/Erdos64EG/FiniteChecks/P13SequentialRatioFailure/P13BooleanRankProductNoGo.lean`.
Its one-coordinate system realizes both Boolean values, so it has the complete
one-coordinate hot/independence certificate, but

```text
543958 ^ 1 <= 111286 ^ 1 * 2
```

is false (`543958 > 222572`). The check uses no `sorry`, new axiom, or
unbounded enumeration.

The incoming node-[32] certificate is weaker still for this purpose: it says
that every admitted determination candidate has an injective coordinate code.
It does not enumerate realized label triples or give their conditional
multiplicities. Consequently contraposition can close node [48] only after a
graph-owned theorem supplies the following additional implication on the
literal incoming residual:

```text
first failed (543958,111286) curvature fibre
  -> an existing node-[32] functional determination certificate.
```

Such a theorem must use a recoverable safe-triple switching action (or an
equivalent fibrewise injection) for the same raw remainder-wedge coordinates.
The current selected-window aggregate cannot instantiate it: its `reglue`
operation changes retained window-package choices while explicitly preserving
the remainder graph, whereas node [31] indexes raw internal wedges of that
remainder graph. No current ledger fact maps every such wedge to a retained
window-package coordinate.

Focused validation on 2026-07-21:

- `lake env lean Erdos64EG/FiniteChecks/P13SequentialRatioFailure/P13BooleanRankProductNoGo.lean`
  succeeds and reports only Lean's standard classical/propositional axioms.
- `lake env lean Erdos64EG/Node48.lean` succeeds.
- `lake env lean Erdos64EG/Node54.lean` fails exactly at the absent
  `Node49Output.forcedPowerFit`; downstream declarations therefore acquire
  `sorryAx` only as elaborator error recovery and are not kernel-verified
  endpoints.
