# Nodes 153--157 literal two-boundary lift audit

Verdict: **FAIL**. The proposed lift from the current `ColdStructuralGerm` to
`PackedBoundariedGluing` is not derivable from the verified predecessor
payload. No manuscript source theorem was changed.

## Provenance matrix

| Used fact | Verified producer | Present? | Verdict |
|---|---|---:|---|
| literal simple deleted-edge return | `InducedPathColdCorridor.returnPath` | yes | usable |
| support bounded by ambient vertex count | `ColdStructuralGerm.supportBound` | yes | not a fixed local bound |
| rejected restored root-cycle length | `ColdStructuralGerm.rootLengthRejected` | yes | only one cycle |
| corridor vertices have no degree above three | `ColdStructuralGerm.allSubcubic` | yes | vertices are cubic under the baseline |
| exactly two boundary interfaces | none | no | blocking |
| every internal incidence is owned by the path piece | none | no | blocking |
| no chord beyond consecutive path edges | none | no | blocking |
| exact reconstruction by normalized gluing | none | no | blocking |
| inherited boundary-degree profile | none | no | blocking |
| target response in every compatible outside context | none | no | blocking |

## Quantifier and ownership attack

`PackedBoundariedGluing.MinimumDegreeCycleReplacement.ProperAtom` requires one
source piece and one outside context whose normalized gluing reconstructs the
entire selected graph. A simple walk proves only that its support list has no
repetition. It does not prove that the graph induced on that support is a
path, and it does not exclude edges from internal support vertices to vertices
outside the support.

On the verified branch every quiet corridor vertex is subcubic, while the
minimal-counterexample baseline gives degree at least three. Hence those
vertices are cubic. An internal path vertex already uses two path incidences;
its third incidence may leave the support or be a chord. Unless that incidence
is classified and owned, the internal vertex cannot be hidden behind a
two-vertex boundary and literal gluing cannot reconstruct the ambient graph.

The smallest schematic countermodel is a cubic graph containing the selected
simple return path with one internal vertex whose third edge leaves the path.
All current germ fields remain true, but deleting the path interior and gluing
a two-terminal canonical path loses that third edge and its endpoint degree.

## CT3 contract audit

| Obligation | Current local length experiment | Literal packed CT3 |
|---|---:|---:|
| finite candidate lengths | yes | insufficient |
| response for restored root cycle | yes | insufficient |
| all target-relevant outside contexts | no | required |
| boundary-degree equality | no | required |
| internal minimum degree three | canonical path interiors have degree two | required |
| local lexicographic decrease | length decrease only | piece rank required |
| graph reconstruction | no | required |
| unchanged cycles avoiding replacement | no | required |

A standalone canonical path has degree-two internal vertices, so it fails
`Piece.InternalBaseline ... 3`. Root-cycle length equivalence does not
transport cycles wholly outside the path or cycles using a third incidence.

## Practicality

`P13ShortPathCT3` is an unconditional standalone local arithmetic experiment,
but its candidate universe is indexed by the ambient return support and its
coordinate universe is `Fin (n+1)`. The long CT17 prototype similarly uses
`Fin (rootLength+1)`. These are not the manuscript's fixed finite cold-state
table and do not satisfy the no-ambient-size-dependent-enumeration rule. The
short experiment is therefore not imported by the accepted Erdős umbrella;
it is retained as a compiling negative prototype because its local theorems
are valid.

## Exact repair-loop re-entry

The missing producer is earlier than the requested lift. It must construct
the manuscript's cold-skeleton corridor, not an arbitrary ambient return path,
and must stop after a fixed number of finite cold states. Its F5 payload must
contain:

1. two actual boundary stubs and a fixed-size support;
2. exact ownership of every support incidence;
3. the capped boundary-degree profile;
4. the fixed target-response coordinate row;
5. either a terminal same-interface representative or two equal repeated
   states producing one; and
6. typed F2/F3/F4 exits for every failure of those conditions.

Only that payload can instantiate a proper atom and literal compression. The
current `ColdStructuralGerm` cannot be strengthened by adding these items as
caller fields.

## Checks

- `lake build Erdos64EG.P13SelectedWindowGermScale`
- `lake build Erdos64EG.P13ShortPathCT3` (standalone negative prototype)
- no `sorry`, `admit`, or new axioms in either file
- `git diff --check`

The next implementation step is the fixed-state cold-skeleton producer and
its exhaustive ownership/first-failure routes, not the invalid two-boundary
lift.

## Fixed D1--D7 state audit (formal stopping obstruction)

The requested dependency order requires the cold cut-state type to have a
cardinality bounded by a constant independent of the ambient order before
F1--F5 are implemented.  The literal/raw reading of the declared-coordinate
signature does not pass that test:

- retaining the two actual active interface vertex identities yields the
  type `V × V`, whose cardinality is exactly `|V|²`;
- D2 retains a connector length in `Nat`, so the raw D1--D2 state contains an
  injective copy of `Nat`.

These are now machine-checked in
`StructuralExhaustion.Core.FixedCutStateObstruction`:

- `rawTwoInterface_card` proves the exact square cardinality;
- `rawTwoInterface_exceeds Q` instantiates `V = Fin (Q+1)` and proves that
  the state count exceeds every proposed constant `Q`;
- `connectorLengthEmbedding` is an injection from `Nat` into the raw D2
  state;
- `rawConnectorLength_not_fintype` proves that this raw D2 representation has
  no finite enumeration;
- `rawConnectorLength_exceeds` and `rawD1D2_exceeds` prove that every proposed
  length cap is exceeded.

The non-Erdos transfer module
`StructuralExhaustion.Examples.FixedCutStateObstruction` executes all three
facts independently of the target problem.

This does **not** prove that a finite cold-state quotient is impossible.  It
proves that the manuscript must specify and verify one: ambient identities
must be replaced by fixed interface roles, connector lengths must be capped
or quotient-coded, and the resulting quotient must be proved complete for
all D1--D7 target responses.  No such code type or response-completeness
theorem currently exists in Core, Graph, Routes, or the Erdős branch.
Accordingly F1--F5 must not be implemented over the raw fields; doing so would
make the claimed `Q_cold` depend on `n` (or be infinite).

Focused verification:

- `lake build StructuralExhaustion.Core.FixedCutStateObstruction`
- `lake build StructuralExhaustion.Examples.FixedCutStateObstruction`

## Intended normalized state (raw obstruction discharged)

The raw obstruction is not the final verdict once the manuscript's intended
normalization is made explicit.  The reusable module
`StructuralExhaustion.Core.FixedTwoBoundaryCutState` now defines the normalized
code using only:

- two boundary *roles* (`Fin 2`), never ambient vertex identities;
- degrees capped at three (`Fin 4`);
- the two selected-window offsets (`Fin 13`);
- the thirteen offset target-response bits (`Fin 13 → Bool`), never the raw
  connector length; and
- a fixed finite D4--D7 local-coordinate alphabet supplied by the producer.

Its exact cardinality is machine-checked as

`4^2 * 13^2 * 2^13 * 2^(card LocalCoordinate)`.

The theorem `state_card_independent_of_ambient` proves that this cardinal is
identical for arbitrary ambient vertex types.  `PrefixObservations`,
`LocalProjection`, and `project` give the structural projection from any
corridor-prefix type.  The one honest remaining semantic obligation is the
fixed finite D4--D7 coordinate alphabet and its graph-derived response map.

`PairContextComparison` is the exact proof-producing both-sides obligation for
one pair.  It must be supplied by structural path-set transport or a local
verified classifier; the framework does not classically search arbitrary
outside graphs.  Given this obligation and equal normalized codes,
`compareEqualCodes` returns either:

1. a concrete response-distinguishing supplied compatible context (typed F2
   residual), or
2. exact response equivalence for that specific pair over the supplied
   compatible-context family, together with equality on all declared local
   coordinates.

The context type is supplied by the consumer.  The theorem neither enlarges
it to arbitrary outside graphs nor treats the coarse state as a CT3 table.
Literal packed compression still requires an actual bounded two-boundary
piece plus target equivalence for every compatible gluing context of that
piece; preferably this will be proved structurally from equality of its
finite internal endpoint-to-endpoint path-length set.

`Erdos64EG.P13FixedColdCutState` specializes the thirteen bits to
`PowerOfTwoLength (connectorLength + offset)` and proves their exact semantics.

Additional focused verification:

- `lake build StructuralExhaustion.Core.FixedTwoBoundaryCutState`
- `lake build StructuralExhaustion.Examples.FixedTwoBoundaryCutState`
- `lake build Erdos64EG.P13FixedColdCutState`

## Structural cold-skeleton prefix (direct-build only)

`StructuralExhaustion.Graph.InducedPathColdSkeleton` now implements the
structural prefix without materializing ambient-size stub/component/path
tables:

- `deletedWindowVertices` is the union of the actual ambient-cubic selected
  P13 supports, and `outsideObject` is the induced remainder after deletion;
- `BoundaryStub` is one literal ambient-cubic window incidence whose other
  endpoint survives in that remainder;
- `component stub` is the quotient-defined connected component of that
  endpoint;
- `TwoStubComponent` retains two distinct stubs, their exact same-component
  proof, and a proof that the second is the successor under an inherited
  `DeclaredSuccessor` relation.  It does not filter or scan every graph stub;
- `CanonicalComponentPath` retains one simple shortest component path and a
  proof that it is least under an inherited path-rank tie-break.  It does not
  enumerate components or paths;
- `observations` projects the two actual interface degrees, the two P13
  offsets, and the retained path length into the normalized fixed-state input;
- `fixedState` observes that length only through the target-offset vector and
  accepts D4--D7 solely through `DeclaredLocalSemantics`.

The exact remaining producer inputs are therefore visible in the types:

1. an earlier proof-producing cyclic successor relation on boundary stubs;
2. a proof-carrying lex-first shortest component path under the declared
   tie-break;
3. the fixed finite D4--D7 coordinate alphabet and its graph-derived response
   map; and
4. literal packed reconstruction plus pair-specific compatible-context
   transport before any CT3 call.

`MissingD4D7Reconstruction` is the sole typed stopping residual at this
frontier.  The module is intentionally not imported by `Graph.lean`,
`StructuralExhaustion.lean`, or the Erdős production umbrella.

Focused verification:

- `lake build StructuralExhaustion.Graph.InducedPathColdSkeleton`
