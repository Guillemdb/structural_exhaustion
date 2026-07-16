# Node [172] repair worksheet: executable owner-block dichotomy

Status: revised separate worksheet after red-team FAIL. This file does not
modify the source manuscript or add a Lean implementation. It resolves the
local construction defects in findings 3--5 and replaces the former informal
CT17/CT10 routes with exact framework instantiations. Those executions expose
a semantic predecessor gap, so the repair is not leaf-total and must not be
merged.

## Defect freeze

- **Defect ID:** `EG-172-OWNER-BLOCK-ROUTE`.
- **Stable node:** proposed node [172], after reviewed Lean node [171].
- **False shortcut rejected:** a repeated selected-window owner gives a
  literal connector cycle, but its length need not be a power of two. A
  triangle is possible.
- **Classification:** the local runner is a level-2 structural repair. Its
  two nonclosing leaves reveal a level-3 routing failure caused by missing
  earlier semantic producers, not by a missing finite search API.
- **Smallest verified ancestor:** node [169]'s computed owner table and first
  owner change, followed by node [171]'s exact zero-check token projection.
- **Immutable blast radius:** proposed descendants of node [171] only.
- **Source manuscript unchanged:** yes.

## Exact directed state

The input path is the exact computed chain

```text
[167] normalized simple return
  -> [168] computed all-inside result
  -> [169] computed owner table and first owner change
  -> [171] computed opposite token-pair projection.
```

Inherited facts are:

- `Gamma'` is a simple ambient walk of edge length `L`;
- `Gamma'.support.length = L + 1 <= Q_base`;
- node [169] stores one exact `OwnedSlot` for every index `0,...,L`;
- selected packed-window supports are pairwise disjoint, hence both owner and
  `Fin 13` position are unique;
- node [171] proves at least one consecutive owner change and retains the
  complete node-[169] source as an index.

Unavailable facts are exactly those excluded by
`rem:p13-cross-window-token-pair-scope`: cold-subfamily membership, a second
connector chosen by semantic response, a compatible offset family, successor
and second remainder stub, component path, D4--D7 response coordinates,
demand, capacity, compression, target closure, and density.

## Exact node-[171] computed predecessor wrapper

Node [172] must not accept an arbitrary `cross` and independently supplied
pair. Its P13 input contract is:

```text
structure ComputedCrossWindowTokenPair (inside) where
  source : P13SameWindowFirstCrossWindow inside
  sourceExact : source = runP13SameWindowPackedOwnerChange inside
  result : P13SameWindowCrossWindowTokenPair source
  runExact : result = runP13SameWindowCrossWindowTokenPair source

computeCrossWindowTokenPair (inside) : ComputedCrossWindowTokenPair inside
```

The canonical constructor sets `source` and `result` to the two displayed
runs and proves both equalities by reflexivity. Node [172] consumes only this
wrapper. Thus its owner table, path, first hit, tokens, and support bound all
come from the actual computed predecessor.

## Generic arbitrary-boundary token producer

`FirstCrossWindow.ofFirstHit` is not reused at later block boundaries. The
required generic Graph/Route contract is:

```text
structure DistinctOwnerEdgeAt (input) (table) (i : Fin input.path.length) where
  distinct :
    (table.slot <i>).window != (table.slot <i+1>).window

structure CrossWindowTokenPairAt (edge : DistinctOwnerEdgeAt input table i) where
  leftSlot  : OwnedSlot object (input.path.getVert i)
  rightSlot : OwnedSlot object (input.path.getVert (i+1))
  leftSlotExact  : leftSlot  = table.slot <i>
  rightSlotExact : rightSlot = table.slot <i+1>
  leftToken rightToken : Token object
  tokensDistinct : leftToken != rightToken
  leftSubtype  : tokenSubtype object leftToken  = .crossWindow
  rightSubtype : tokenSubtype object rightToken = .crossWindow
  leftOriented : selectedWindow object leftToken.window leftToken.position
      = input.path.getVert i
    and leftToken.neighbor = input.path.getVert (i+1)
  rightOriented : selectedWindow object rightToken.window rightToken.position
      = input.path.getVert (i+1)
    and rightToken.neighbor = input.path.getVert i
  sameLiteralEdge :
    s(input.path.getVert i, input.path.getVert (i+1))
      = s(input.path.getVert (i+1), input.path.getVert i)

tokensAt (edge) : CrossWindowTokenPairAt edge
additionalChecks(tokensAt) = 0.
```

The proof uses only the two stored slots, path adjacency, disjoint packing
supports, and the fact that each opposite endpoint remains in the packed
union. It is the same local argument as node [169]'s first-hit constructor
with the first-hit premise removed. No lookup or scan is rerun.

## Executable block compression and least-repeat runner

Let `o_i` be the owner projection of the stored slot at path index `i`. The
executable compressor scans consecutive indices once and returns maximal
nonempty intervals

```text
[s_0,e_0], ..., [s_(K-1),e_(K-1)]
```

with constant owner `omega_j`, consecutive owners unequal, ordered disjoint
intervals, and union `{0,...,L}`. The first node-[171] change proves `K >= 2`.

The least-repeat runner scans blocks in increasing `b` and, for each `b`,
compares `omega_b` with `omega_0,...,omega_(b-1)` in increasing order. Its
result type is:

```text
inductive OwnerBlockResult
| repeated
    (b : Fin K) (a : Fin b)
    (prefixDistinct : PairwiseDistinct (omega_0,...,omega_(b-1)))
    (ownerEqual : omega_a = omega_b)
    (firstAtB : for every c < b, owner omega_c does not repeat earlier)
    (leastAtA : for every c < a, omega_c != omega_b)
| allDistinct
    (distinct : PairwiseDistinct (omega_0,...,omega_(K-1))).
```

`prefixDistinct` makes `a` the unique earlier equal owner. The runner has no
caller predicate and returns equality with its reference execution.

### Exact check ledger

Block compression performs exactly `L` owner-equality checks. With the nested
declared-order repeat scan:

- on `repeated b a`, it performs exactly

  ```text
  L + b*(b-1)/2 + (a+1)
  ```

  owner-equality checks;
- on `allDistinct`, it performs exactly

  ```text
  L + K*(K-1)/2
  ```

  checks.

Both are at most `L + K*(K-1)/2 <= (L+1)^2`. Block materialization uses
`O(L)` memory. The run is two finite list traversals, has no recursion or
re-entry, and reads no ambient universe.

## Oriented connector-cycle theorem

For the least repeated pair `a < b`, let

```text
u = Gamma'[e_a],       alpha = its stored position in W,
v = Gamma'[s_b],       beta  = its stored position in W,
g = s_b - e_a >= 2,   W = omega_a = omega_b.
```

No internal vertex of `Gamma'[e_a .. s_b]` has owner `W`. Simplicity gives
`u != v`, so `alpha != beta` and
`d = positionDistance alpha beta` lies in `{1,...,12}`.

The reusable theorem signature is:

```text
ownerBlockConnectorCycle
  (source : FirstRepeatedOwner ...)
  (LengthOK : Nat -> Prop)
  (accepted : LengthOK (g + positionDistance alpha beta)) :
  CycleWithLength object.graph LengthOK
```

It is constructed in two exhaustive orientation-safe cases.

1. **`g = 2`.** The unique middle path vertex `x` is outside `W` and is
   adjacent to both `u` and `v`. Order `alpha,beta` by `min/max` and use
   `InducedPathAttachment.cycleOfAttachments`. The resulting closed walk is
   the attachment edge, the ordered embedded-window segment, and the return
   attachment edge; its length is `2+d`.
2. **`3 <= g`.** Let `x = Gamma'[e_a+1]`, `y = Gamma'[s_b-1]`, and let
   `connector` be the oriented subwalk from `x` to `y`. It is a simple path,
   `x != y`, and every vertex in its support is outside `W`. Apply
   `InducedPathConnectorCycle.connectorCycle`. Its literal closed walk is

   ```text
   connector.append
     (InducedPathBridge.unorderedBridge W y x beta alpha yAdj xAdj)
   ```

   where the second walk runs from `y` back to `x`; its embedded-window
   portion is the required reverse orientation. The existing theorem proves
   endpoint typing, both attachment adjacencies, path simplicity, tail-support
   disjointness, `IsCycle`, and exact length
   `connector.length + 2 + d = g+d`.

Thus the former unoriented-union gap is removed. The exact bounds are

```text
3 <= g+d <= L+12 <= Q_base+11.
```

The existing P13 CT1 adapter may consume the returned literal cycle when
`g+d = 2^k`, `k>=2`.

## Exact local dichotomy

Node [172] returns exactly one of:

1. `DyadicConnector`: the first repeated owner, the literal cycle above, an
   exponent `k>=2`, and exact length `2^k`; CT1 returns C1.
2. `NonDyadicConnector`: the same literal cycle, exact base `g`, exact offset
   `d in {1,...,12}`, exact length `g+d`, and proof `g+d notin Pow`.
3. `AllDistinctOwnerChain`: `2 <= K <= L+1 <= Q_base`, the exact maximal
   blocks, pairwise-distinct owners, and `tokensAt` for every one of its
   `K-1` boundaries.

This split is executable and total. Only the first constructor closes.

## Concrete CT17 execution on the non-dyadic connector

The strongest CT17 input constructible from the predecessor has this exact
API instance:

```text
Target         = the explicitly enumerated powers of two in [4,Q_base+11]
Offset         = Unit
Position scale = Unit
Value          = Nat
targetValue t  = t
blockValue ctx () () = ctx.state.connectorLength
orbitValue ctx _ ()  = ctx.state.connectorLength
Compatible ctx _ _   = True
finiteScaleLimit      = Q_base
Input.scale           = ctx.state.baseLength g
```

The branch context is indexed by the exact `NonDyadicConnector`; no route seed
may replace it. The target subtype enumeration is obtained by filtering the
finite interval `[4,Q_base+11]` with the decidable power-of-two predicate;
offsets and positions use the explicit singleton enumerator.

Because `g <= L <= Q_base`, CT17 takes its finite-scale branch. Compatibility
is exhaustive and true. The unique position survives exactly because
`g+d notin Pow`. Therefore the exact framework result is

```text
terminal = CT17.terminal.residual.survivors
survivorList = [()]
```

with validity supplied by `CT17.run_verified` and totality by
`CT17.run_total`. Incompatibility, exhausted, target-hit, and orbit are
unreachable for this indexed input.

This concrete CT17 run is branch-total but makes no progress: its survivor is
definitionally the same non-dyadic connector. It is therefore rejected as a
consumer rather than registered as a stationary handoff.

### Exact missing CT17 predecessor

A useful instance of manuscript `lem:cold-short-self-return-filter` requires
one outside self-return together with compatible literal completions through
the whole offset family `{0,...,12}`. Node [171] supplies only the single
fixed internal distance `d=|alpha-beta|`. It cannot prove compatibility for
any other offset.

The earliest missing semantic producer is node [160]'s 91-coordinate
completion-state realization. Even that producer would still need the
branch-specific cold corridor data of node [153]: cold-window membership,
successor boundary stub, second stub, component path, and the first-failure
response clauses from `def:cold-corridor-first-failure`. None is an ancestor
of the all-inside node-[171] branch. Supplying `Compatible` as a caller
predicate would invent precisely the semantics those nodes are meant to
prove.

## Concrete CT10 execution on the all-distinct chain

Let each boundary index `j : Fin (K-1)` be a datum. Its exact stored slots
define the finite observable class

```text
Class = Fin 13 x Fin 13
classOf j = (right position of block j,
             left position of block j+1).
```

Use the product `FinEnum`, and define the exact CT10 capability by

```text
Datum     = Fin (K-1)
Class     = Fin 13 x Fin 13
Promotion = Class
classes   = product enumeration in declared lexicographic order
Direct _  = False
promote c = c
Input.data = ordered collection of every boundary index j.
```

Using boundary indices rather than raw position pairs gives the required
`OrderedCollection.Nodup` even when two boundaries share one class. The branch
context is inherited definitionally through `CT10.Trigger` and
`CT10.Input.ofTrigger`.

The exact CT10 execution is total and has two reachable outcomes:

- `.promoted`: the framework returns the first lexicographic position-pair
  class absent from the actual chain and promotion equal to that class;
- `.exhaustive`: every one of the 169 position-pair rows is populated.

The `.direct` terminal is impossible because `Direct=False`. These statements
use `CT10.run_verified`, `CT10.run_total`, and, on a complete table,
`run_terminal_exhaustive_of_noDirect_of_populated`.

Neither result closes the graph branch. A missing position pair is not a
target, defect, compression, or rank datum. Complete population is not a C5
impossibility; CT10's verified statement says only that every class has a
datum. Using `CT10.ExhaustiveClassification` with the observed classes would
likewise certify table completeness, not mathematical contradiction. Both
outcomes are retained as exact audit results and are rejected as consumers.

### Exact missing CT10 predecessor

For a closing CT10 instance, `Direct` and `promote` must be derived from an
earlier semantic classification. The available position pair and opposite
tokens contain no target-response, same-interface, exit, or compression
meaning. The first missing semantic producer is again node [160]'s D4--D7
completion-state system. To obtain the manuscript's actual finite consumer,
it must be combined with node [153]'s cold-corridor first-failure producer and
the same-interface table used at nodes [154]--[157]. Those clauses classify a
state as target hit, target defect, compression, named handoff, or bounded
germ. They are not ancestors of node [171], and cold membership may not be
inferred from ambient-cubic ownership.

## Both-sides and leaf-totality table

| Branch | Exact local output | Concrete framework execution | Result |
|---|---|---|---|
| repeated owner, dyadic length | oriented literal cycle of length `2^k` | existing CT1 cycle adapter | C1 |
| repeated owner, non-dyadic length | exact cycle, `g`, `d`, and rejection | concrete singleton CT17 above | exact one-element survivor; no progress |
| all owners distinct | exact bounded chain and every boundary token pair | concrete 169-class CT10 above | missing-class promotion or populated table; neither closes |

The local invariant passes the both-sides measurability test, but the complete
proof branch is **not leaf-total from nodes [169]--[171]**. CT17 and CT10
cannot manufacture the missing completion/response semantics. A leaf-total
repair becomes possible only after an earlier graph-owned producer supplies:

```text
CompatibleOffsetFamily
  = literal cycle completion for every advertised offset,

SemanticOwnerBoundaryState
  = finite D4--D7 target-response/exit data with proved realization,
    persistence, and a classwise target/defect/compression/handoff theorem.
```

The manuscript locates these obligations at [160] and the cold-corridor
first-failure path [153]--[157]. They cannot be added as fields of node [172]
or supplied by its caller.

## Practicality and locality

- owner-block compression: exactly `L` equality checks;
- least-repeat scan: exact formulas above, total at most `(L+1)^2` checks;
- arbitrary-boundary tokens: zero new primitive checks after stored slots;
- cycle construction: projections of one return subwalk and one 13-position
  window segment;
- concrete CT17 diagnostic: finite target interval filter times one offset and
  one position; no orbit enumeration;
- concrete CT10 diagnostic: `K-1` local data and 169 fixed classes;
- all computation is local to the supplied return and stored slots;
- no graph, completion, selected-window universe, or cold family is
  enumerated;
- no recursion or cyclic handoff is proposed.

## Lean statements and transfer fixtures required before re-audit

The eventual generic implementation must contain:

1. `ComputedCrossWindowTokenPair` and its canonical exact constructor;
2. `DistinctOwnerEdgeAt`, `CrossWindowTokenPairAt`, and `tokensAt`;
3. executable block compression, least-repeat decision, exact reference-result
   theorem, and the two exact check formulas;
4. `ownerBlockConnectorCycle`, using `cycleOfAttachments` when `g=2` and
   `InducedPathConnectorCycle.connectorCycle` when `g>=3`;
5. non-Erdos fixtures for `g=2`, `g>=3`, repeated dyadic, repeated
   non-dyadic, and all-distinct outcomes;
6. diagnostic CT17 and CT10 instantiations proving the exact survivor and
   promoted/exhaustive outcomes above.

These contracts resolve the red-team construction findings without claiming
that diagnostic framework totality is theorem closure.

## Disposition

The revised node-[172] bookkeeping and geometry contract is construction-
ready. A leaf-total manuscript repair is not possible from the verified
node-[171] predecessor state. The precise missing mathematical provenance is
the completion-state realization at [160] together with a branch-compatible
cold-corridor semantic producer of the form proved only conditionally at
[153]--[157]. The original manuscript and Lean graph remain unchanged.
