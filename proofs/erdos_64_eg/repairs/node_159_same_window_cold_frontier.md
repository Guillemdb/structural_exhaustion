# Proposed node [159]: same-window cold corridor frontier

This is a separate repair sketch only. It does not edit Lean sources, the
manuscript, theorem companion, diagram, generated status map, or implementation
log. It is conditional on node `[158]` passing its implementation and review
gate. Until then, node `[159]` is **not green** and has no synchronized edge.

The former provisional node-`[159]` realization draft is retired.  The stable
reservation is `[158]` for the actual-attachment cold fork, `[159]` for this
same-window frontier, and `[160]` for the still-white 91-bit realization
obligation recorded in `repairs/node160_91_bit_realization_obligation.md`.

## Intended statement

For one literal
`window : P13SelectedConnectorWindow ctx`, execute exactly
`routeSelectedWindowCorridor ctx window` and flatten its dependent result into
four honest graph-owned constructors:

1. a high-degree position in the selected window;
2. a dyadic target hit on the canonical deleted-edge return;
3. a high-degree event at the first failing corridor stage; or
4. a quiet `ColdStructuralGerm` for the same canonical stub.

No outcome, external stub, return corridor, first-hit stage, or germ is
accepted from the caller. No constructor states a density estimate.

## Exact proposed output

The thin Erdős-owned output should have the following shape (names may be
adjusted mechanically, but not the fields):

```lean
inductive P13SameWindowColdFrontier
    (ctx : Core.MinimalCounterexampleContext PackedProblem PackedTarget)
    (window : P13SelectedConnectorWindow ctx) where
  | surplus
      (position : Fin 13)
      (high : 3 < ctx.G.object.degree (window.1 position))
  | dyadicTargetHit
      (stub : InducedPathColdCorridor.CubicStub ctx.G.object)
      (sameWindow : stub.window = selectedConnectorWindowIndex window)
      (hit : Core.FiniteSearch.FirstHit
        ((InducedPathColdCorridor.firstFailureProfile
          (p13SelectedWindowCorridorProducer ctx) PowerOfTwoLength
          powerOfTwoLengthDecidable).stages stub).values
        ((InducedPathColdCorridor.firstFailureProfile
          (p13SelectedWindowCorridorProducer ctx) PowerOfTwoLength
          powerOfTwoLengthDecidable).Event stub))
      (proof : InducedPathColdCorridor.F1
        (p13SelectedWindowCorridorProducer ctx) PowerOfTwoLength
        stub hit.value)
      (target : InducedPathColdCorridor.Producer.TargetHit
        (p13SelectedWindowCorridorProducer ctx) PowerOfTwoLength)
  | corridorHighDegree
      (stub : InducedPathColdCorridor.CubicStub ctx.G.object)
      (sameWindow : stub.window = selectedConnectorWindowIndex window)
      (hit : Core.FiniteSearch.FirstHit
        ((InducedPathColdCorridor.firstFailureProfile
          (p13SelectedWindowCorridorProducer ctx) PowerOfTwoLength
          powerOfTwoLengthDecidable).stages stub).values
        ((InducedPathColdCorridor.firstFailureProfile
          (p13SelectedWindowCorridorProducer ctx) PowerOfTwoLength
          powerOfTwoLengthDecidable).Event stub))
      (handoff : InducedPathColdCorridor.Producer.SurplusHandoff
        (p13SelectedWindowCorridorProducer ctx))
  | quiet
      (stub : InducedPathColdCorridor.CubicStub ctx.G.object)
      (sameWindow : stub.window = selectedConnectorWindowIndex window)
      (noEvent : forall stage,
        stage in
          ((InducedPathColdCorridor.firstFailureProfile
            (p13SelectedWindowCorridorProducer ctx) PowerOfTwoLength
            powerOfTwoLengthDecidable).stages stub).values ->
        not ((InducedPathColdCorridor.firstFailureProfile
          (p13SelectedWindowCorridorProducer ctx) PowerOfTwoLength
          powerOfTwoLengthDecidable).Event stub stage))
      (germ : InducedPathColdCorridor.Producer.ColdStructuralGerm
        (p13SelectedWindowCorridorProducer ctx) PowerOfTwoLength stub)
```

In actual Lean syntax the `quiet` quantifiers use `∀`, `∈`, and `¬`; ASCII is
shown above only to keep this sketch robust outside a code implementation.
The `corridorHighDegree` constructor may also retain the `f4` proof and the
three priority-negation fields from `EventData.f4`. Retaining them is
preferable: together with `hit.beforeAbsent`, they certify that this is the
canonical first corridor event and not merely an arbitrary high-degree
vertex.

The target and handoff payloads already store the identical `stub`. The thin
flattening theorem should additionally expose these definitional equalities
if dependent pattern matching does not reduce them automatically.

## Sole construction

The constructor is one total dependent match and introduces no reusable
routing logic:

```lean
noncomputable def runP13SameWindowColdFrontier (ctx) (window) :
    P13SameWindowColdFrontier ctx window :=
  match routeSelectedWindowCorridor ctx window with
  | .surplus position high => .surplus position high
  | .corridor stub sameWindow result =>
      match result with
      | .germ noEvent germ => .quiet stub sameWindow noEvent germ
      | .first hit event =>
          match event with
          | .f1 proof target =>
              .dyadicTargetHit stub sameWindow hit proof target
          | .f2 _ proof impossible => impossible.elim
          | .f3 _ _ proof impossible => impossible.elim
          | .f4 _ _ _ proof handoff =>
              .corridorHighDegree stub sameWindow hit handoff
```

The `f2` and `f3` branches eliminate their `Empty` data. This is exact because
the existing `firstFailureProfile` defines `F2` and `F3` to be `False` and
their data types to be `Empty`. The `f1` payload is a literal cycle whose
length satisfies `PowerOfTwoLength`; the `f4` payload is an actual corridor
vertex with degree strictly above three.

This node must import and reuse `P13SelectedWindowCorridor`; it must not
reimplement stub selection, bridge deletion, return construction, or the
first-failure scan. Because the flattening is application-specific and adds no
new route principle, no generic transfer fixture is required.

## Provenance ledger

Every output is indexed by the original `ctx` and `window`.

- `surplus` uses the literal vertex `window.1 position`.
- Every other constructor retains the canonical `stub` selected by
  `InducedPathColdStubSelection.classify` and the proof
  `stub.window = selectedConnectorWindowIndex window`.
- The stub stores its exact external-incidence token, hence its window,
  `Fin 13` position, external neighbour, adjacency proof, and ambient-cubic
  proof.
- `dyadicTargetHit` and `corridorHighDegree` retain the canonical `FirstHit`.
  Its `beforeAbsent` theorem preserves the clean prefix.
- `quiet` retains the exhaustive `noEvent` proof and the germ constructed by
  `germOfClear`; it does not accept a caller-supplied germ.

The node therefore preserves the complete chain

```text
ctx
  -> CT12-selected literal window
  -> selectedConnectorWindowIndex
  -> canonical external-incidence stub
  -> canonical deleted-edge return
  -> canonical first event or quiet structural germ.
```

## Semantic limits

The quiet constructor is exactly
`Producer.ColdStructuralGerm`. Its only substantive fields are:

- support length at most the ambient vertex count;
- rejection of the root cycle length as a target length; and
- absence of a high-degree vertex on the corridor stages.

It is **not** a `ColdBoundedGerm`. Node `[159]` supplies no constant support
bound, local smaller replacement, context-response equality, target-context
coverage, bounded overlap, or disjoint germ family. In particular, it does not
prove manuscript nodes `[153]`--`[157]` quantitatively and does not imply any
density statement.

The two high-degree constructors are surplus handoffs only. They are not
target hits, density contradictions, or closures unless a later typed consumer
pays for them.

## Precise local work bound

Let

```text
n = ctx.G.object.input.vertices.card,
p = packingNumber ctx.G.object,
sigma_W = windowSurplus ctx.G.object,
T = (tokens ctx.G.object).card = 15*p + sigma_W.
```

For a single supplied window, the explicit finite scans used by the existing
route have these bounds:

1. the degree classifier inspects the thirteen positions; its current
   non-cubic witness extraction may scan the same thirteen-position list once
   more, so at most `26` position checks;
2. on the cubic side, canonical stub selection filters the existing global
   token schedule once, so at most `T = 15*p + sigma_W` token-membership
   checks; and
3. the first-failure runner performs exactly one combined event check per
   vertex of the canonical simple return support, hence at most `n` checks.

Thus the visible finite-scan budget for one call is at most

```text
26 + T + n = 26 + 15*p + sigma_W + n
```

combined local checks. The result stores only one window, one stub, one simple
return, and one first-hit or germ; it materializes no family of graphs,
contexts, completions, or corridors.

Audit caveat: `DartReturn.ofNotBridge` currently obtains the simple return by
classical choice from proved reachability. The bound above is the exact budget
of the explicit repository scans, not a runtime bound for extracting that
chosen path. If executable evaluation becomes a merge requirement, replace
that choice internally by a finite graph reachability/BFS producer with an
explicit graph-local bound; do not add a caller-supplied return path to this
node.

## Status and merge gate

Proposed edges after node `[158]` is integrated and reviewed:

```text
[158] actual-attachment-cold selected window
   -> [159] same-window cold corridor frontier
      -> surplus handoff
      -> dyadic target hit
      -> corridor high-degree handoff
      -> quiet ColdStructuralGerm (open downstream residual)
```

Node `[159]` may become green only when:

1. node `[158]` is green and supplies the exact same selected-window object;
2. the thin four-constructor flattening compiles;
3. exhaustive coverage and same-window/stub preservation theorems compile;
4. the affected Erdős package builds; and
5. review confirms that the quiet branch has not been promoted or counted.

Until all five gates pass, `[159]` remains a proposed white node. Shared TeX,
web, and status files must not be edited from this sketch.
