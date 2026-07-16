# Node [158] actual-attachment classifier fork: repair and red-team sketch

This is a separate repair sketch only. It does not edit the manuscript,
Lean sources, theorem companion, diagram, generated status map, or
implementation log. The frozen manuscript is
`proofs/erdos_64_eg/erdos_64_proof.tex`, SHA-256
`6cea87715450176e2b3e611a347c7147764730866c7174122e5be0445235c671`.

## Verdict

**PASS, with a mandatory reformulation.** Node `[158]` may be added as a
green, graph-owned typed producer which classifies the *actual thirteen-bit
attachment system* on every CT12-selected window. It may not be presented as
the negative side of the missing 91-coordinate realization theorem.

**FAIL as a dichotomy.** The propositions

1. the missing 91-coordinate completion system is realizable, and
2. the actual thirteen-coordinate attachment system is cold

are neither complements nor mutually exclusive. They concern different
systems. In fact, the second proposition is already forced by the forbidden
four-cycle argument, independently of whether a future 91-coordinate system
can be constructed. A decision node with these as its yes/no labels would be
logically false.

The corrected diagram is therefore a fork of obligations, not a mathematical
dichotomy:

```text
                         +--> [22] 91-coordinate completion/gluing (WHITE)
[21] exact CT12 prefix --+
                         +--> [158] actual 13-bit classifier (GREEN producer)
                                  |
                                  +--> [151] after near-cubic join
```

The old `[21] -> [22]` branch remains explicitly white. Node `[158]` neither
proves nor refutes it.

## Exact graph-owned producer

For each
`window : SelectedP13Window ctx`, use exactly
`p13ActualAttachmentSystem ctx window.1`:

- its coordinates are the thirteen literal path positions `Fin 13`;
- its states are actual ambient vertices outside that literal window;
- its response bit is literal adjacency to the selected path position; and
- its state and coordinate universes are finite and graph-owned.

The missing thin application constructor has the following intended shape:

```lean
noncomputable def p13ActualAttachmentData
    {ctx : Core.MinimalCounterexampleContext PackedProblem PackedTarget}
    (node21 : VerifiedP13MultiScaleCurvaturePrefix ctx) :
    P13LocalBooleanData ctx node21 where
  system := fun window => p13ActualAttachmentSystem ctx window.1
```

Its `family.classifyWindow` call is the existing executable finite classifier;
it does not decide the existence of an unconstructed system. The following
thin theorems are the implementation gate for green status:

1. every returned hot entry is impossible by
   `p13ActualAttachment_hot_impossible node21 window certificate`;
2. `hotWindows = []`;
3. `coldWindows.length = p13 ctx`, using the exact partition theorem; and
4. every cold entry retains its original `SelectedP13Window ctx` and its
   explicit missing thirteen-bit adjacency assignment.

Thus `[158]` is an executable classifier producer with an exhaustive typed
output. Its semantic conclusion is stronger than a mere hot/cold case split:
all selected windows are *actual-attachment cold*. This does not make them
91-barrier-cold.

## Exact ID, edges, and status

| Item | Proposed meaning | Status after the thin Lean gate |
|---|---|---|
| `[158]` | classify all CT12-selected windows using the actual `Fin 13` attachment system; eliminate the impossible hot constructor | green |
| `[21] -> [158]` | pass the exact selected packing and node-21 legality provenance | green |
| `[21] -> [22]` | construct the 91-coordinate completion system and prove commuting realization | white |
| `[158] -> [151]` | pass exact selected cold windows to the ambient-cubic filter | typed, but requires the near-cubic join |
| `[144] -> [151]` | pay the total-surplus / `o(n)` non-cubic loss | white until the spine estimate is proved |
| `[151] -> [152]` | retain ambient-cubic windows and apply the exact `15`-stub / `13`-excess arithmetic | green locally |
| `[152] -> [153]` | select actual external incidences and run the graph-owned first-failure corridor | partially green; quantitative bounded-overlap extraction remains open |
| `[153] -> [154]` | promote an ambient-finite structural germ to a uniformly bounded germ | white |
| `[154] -> [155]` | G1 dyadic target hit | green only for the already typed bounded-germ input |
| `[154] -> [156]` | G2 target defect / exit / handoff | typed producer, closing consumer still open |
| `[154] -> [157]` | G3 or same-interface compression | green only for the already typed bounded-germ input; uniform production remains open |

No existing manuscript or web node changes color merely because this sketch
exists. In particular, `[22]`, `[144]`, `[151]` as an asymptotic assertion,
and the quantitative claims in `[153]`--`[157]` stay white or partial until
their exact missing inputs are implemented.

## Packing and window provenance into [145]--[157]

The classifier never replaces a selected window by a code or an existential
witness. A cold entry stores

```text
cold.window : SelectedP13Window ctx
```

and therefore still carries literal membership in `p13Windows ctx`. The
existing adapter

```text
selectedWindowIndex cold.window : WindowIndex ctx.G.object
```

converts precisely that same CT12 member to the graph ledger index. A
`ClassifiedColdCubicStub` then retains:

- the classifier-produced cold object;
- its exact `Fin 13` position;
- an actual ambient external neighbour and incidence proof; and
- the ambient-cubic proof for the same window.

Its `toGraphStub` forgets only the Boolean classifier evidence. It preserves
the selected window, position, external endpoint, and cubic proof consumed by
the node-`[153]` corridor runner. Consequently `[158]` can enter the geometric
cold corridor without a provenance gap.

The required downstream joins remain explicit:

- `[151]` needs the minimum-degree-three baseline and the near-cubic
  total-surplus estimate. The graph theorem
  `nonAmbientCubic_card_le_totalSurplus` gives the exact finite loss, but it
  does not turn that loss into `o(n)` by itself.
- `[152]` has exact local arithmetic for an ambient-cubic selected window:
  fifteen external stubs and thirteen after the two transit ends.
- `[153]` has a total graph-owned first-failure producer, but its quiet output
  has only an ambient-size support bound. A uniform `D_cold`, bounded germ,
  and bounded-overlap extraction are not yet consequences.
- `[154]`--`[157]` may consume a genuinely bounded germ; they cannot assume
  that the node-`[153]` structural germ is bounded by a constant.

## Semantic firewall

Write the new family, if needed, as `C_actual`. Do not identify it with the
manuscript family `C_91` used in the live-hot entropy and cold-mass algebra.
The missing assignment stored by `[158]` is a thirteen-bit adjacency vector,
not a failed 91-barrier completion pattern. Therefore `[158]` does not justify:

- node `[148]`'s 91-coordinate entropy cap;
- node `[149]`'s density ceiling;
- node `[150]`'s stated hot-failure lower bound for `C_91`; or
- any substitution of `C_actual` into those formulas without a new theorem
  rewriting the definitions and checking every consumer.

It can bypass `[145]`, `[148]`, and `[150]` only for the separate geometric
statement that every selected window is actual-attachment cold. The geometric
route may then join the near-cubic input at `[151]`.

## Local computation audit

For an ambient graph on `n` vertices, one selected system has exactly thirteen
coordinates, at most `n` actual outside-vertex states, and `2^13 = 8192`
assignments. Across `p13 ctx` selected windows, the classifier performs at
most

```text
8192 * n * p13(ctx) <= 8192 * n^2
```

assignment/state vector comparisons, each comparing thirteen adjacency bits.
This is an explicit local polynomial scan. It enumerates no graph family,
completion family, subgraph universe, or compatible-context universe.

## Merge gate

Node `[158]` may be synchronized as green only after the canonical data
constructor and the four thin all-cold/provenance theorems above compile in
the Erdős package, with a non-Erdős transfer fixture if a new reusable theorem
is added. The diagram must show the 91-coordinate realization edge as a
separate white branch. Any version labeling actual coldness as failure of the
91-coordinate realization, or claiming `[151]`--`[157]` closed, fails this
red-team audit.
