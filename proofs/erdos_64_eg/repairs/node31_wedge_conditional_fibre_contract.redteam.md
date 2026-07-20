# Red-team audit: node [31] wedge conditional-fibre contract

## Baseline

- Repair sketch: `node31_wedge_conditional_fibre_contract.md`
- Original manuscript SHA-256:
  `215248521b7dbc6519076d506101b80a1c9a8425ee5c13b48a4ec52df21d2e10`
- Failed interface: node `[31]` functional quotient rank to node `[48]`
  `543958/111286` product cost.
- Current verdict: **FAIL**.

## Provenance matrix

| Used fact | Producer | Earlier on this path? | Independent? | Verdict |
|---|---|---:|---:|---|
| Raw remainder wedges | nodes `[29]`--`[30]` | yes | yes | valid |
| Exact counts `543958`, `111286` | node `[21]` finite table | yes | yes | valid |
| Functional quotient surviving family | node `[31]` rank definition | local | yes | valid |
| Compatible global completion | node `[21]` sequential hot ledger | yes | yes | valid |
| Global completion is target-avoiding | minimal residual / `P13GlobalGraphCompletion.targetAvoiding` | yes | yes | valid |
| Wedge-safe switching closure of the global carrier | no producer | no | n/a | blocking |

## Quantifier attack

The proposed switch has type

```text
F_{i+1} x Fin 543958 -> F_i x Fin 111286,
```

where every `F_i` is a filtered view of the incoming global-completion
carrier. The source carrier records only target-avoiding global completions.
The `543958` table, however, counts all locally safe label triples; it does not
state that all those triples extend to target-avoiding global completions of
the same residual.

Consequently the proposed switch exchanges

```text
for every locally safe triple there is a compatible target-avoiding state
```

for the proved statement

```text
every stored target-avoiding state has one locally safe/flat triple.
```

These quantifiers are not equivalent. The former is exactly the missing
simultaneous extension theorem.

There is a second incompatibility. `P13GlobalGraphCompletion` contains a field

```text
targetAvoiding : not PackedTarget object.
```

Thus a local variation whose curvature response creates the target cannot be
a state of this carrier. The safe table intentionally contains both flat and
curvature-positive triples. Hence the full safe alphabet cannot act internally
on the target-avoiding carrier without an additional partial-state or
extension semantics.

## Branch and invariant audit

- Positive side: a genuine prefix-switching certificate would pay the desired
  product cost and Core would telescope it correctly.
- Negative side: the sketch claims that any failed conditional step yields
  the existing functional rank-drop payload. No theorem establishes this.
  A cardinality failure does not by itself construct an admissible,
  context-universal, represented functional quotient.
- Measurability: prefix filtering is local once an `accepts` predicate exists.
  The missing extension/switch is not currently measurable from the stored
  global-completion carrier.
- Cross-branch leakage: none detected.
- Added assumption: obligations 3--7 of the sketch would become an added
  assumption if placed directly in `Node31Facts`.

## CT obligations

| CT instance | Trigger | Unfilled schema | Verdict |
|---|---|---|---|
| `Core.ConditionalFibreRank` | exact finite state carrier and wedge schedule | graph-semantic `accepts`, every paying step, terminal nonemptiness | blocking |
| CT15 rank-drop consumer | first failed conditional step | failure-to-functional-determination certificate | blocking |
| full-rank cost consumer | certified carrier output | none after the output exists | pass |

## Practicality

The proposed checker would be polynomial in the supplied carrier and wedge
schedule. Practicality is not the blocker. Constructing a new carrier of all
safe partial assignments would violate the absolute residual-carrier rule and
could be exponentially large if materialized.

## Findings

### Blocking

1. The incoming carrier contains target-avoiding global completions, whereas
   the safe alphabet contains local choices that may create the target.
   Therefore the proposed full safe switching action is not internal to the
   literal carrier.
2. The paper and current Lean chain do not prove that a failure of the
   conditional safe/flat inequality creates the functional admissible quotient
   required by the existing rank-drop branch.
3. Functional label-injectivity does not supply the missing extension and
   recovery maps.

### Required cleanup

The sketch must not describe `States(B31)` as both the target-avoiding global
carrier and the safe pre-filter carrier. These are distinct semantic objects.

## FAIL disposition

The exact obligation returned to the repair loop is:

> Find an existing residual-owned partial-state carrier, preceding target
> filtering, on which the complete safe label alphabet acts by recoverable
> local switches; or prove a symbolic encoding theorem that obtains the same
> cardinality inequality without materializing such a carrier.

The current repository exposes such a carrier for retained packed-window
connector packages, but not for raw remainder wedges. Until a graph-level
wedge projection and preservation theorem is derived, Core/CT15 plumbing
cannot be instantiated soundly at node `[31]`.

No source-manuscript or node implementation change is approved by this audit.
