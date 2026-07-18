# Erdős--Gyárfás 64 original-flow repair register

## Nodes [129] and [131]: missing baseline-spine producer

The original node `[129]` is stronger than the currently verified CT15
prefix.  In `original_erdos_64_proof.tex` it asserts, on the output of node
`[128]`, both

\[
  \mathcal A_0=\mathcal P_{\rm exc}
  \qquad\text{and}\qquad
  E_{\rm spine}(n)\le C_E n
\]

for an independently target-testable family
`\(\mathcal I_{\rm spine}\)` satisfying
`\(|\mathcal I_{\rm spine}|\ge B_0(n)-E_{\rm spine}(n)\)`.
Node `[128]` supplies the selected excess ports and their proof-carrying local
return/suppression supports.  It does not supply a family of approximately
`\(B_0(n)=\frac32n\log_2 n+O(n)\)` independent target coordinates, nor an
injection from their Boolean states into the cubic skeleton family.

The present Lean profile therefore uses the only unconditional instance
available from those predecessors: the empty coordinate family.  Its exact
deficit is the full `baselineSpineBitBudget`, of order `\(n\log n\)`, not
`\(O(n)\)`.  This verifies the definition with its exact deficit but does not
verify the original node `[129]` cell.

The original node `[131]` is consequently blocked as well.  Its claimed
free-pair inequality

\[
 |\Pi_{\rm free}|\le E_{\rm spine}(n)
   +\left(\frac{\sigma(G)}2+1\right)\log_2 n
\]

uses the missing linear-deficit family as its principal input.  The later
window, remainder, and curvature packages cannot be imported here: they are
proved only after the near-cubic spine which nodes `[129]`--`[144]` are meant
to establish.  Doing so would be circular.

The current live manuscript's replacement of `[131]` by a `freeAnchor` token
route is useful exact bookkeeping, but it is not the original node `[131]`.
It also changes the downstream `[136]`/`[137]` accounting from the original
24-role blocked-pair ledger and `D_all` decision to a 25-role complete-pair
ledger and `D_25` decision.  Under the immutable-original specification these
nodes must not be counted as implementations of the original cells merely
because the replacement route compiles.

The first missing theorem in dependency order is therefore:

> From the exact node-`[128]` residual, construct a declared independently
> target-testable family `\(\mathcal I_{\rm spine}\)` with
> `\(B_0(n)-|\mathcal I_{\rm spine}|\le C_E n\)`.

No theorem currently in the predecessor cone proves this statement.  It may
not be supplied as an author premise or manufactured by declaring target
dependence to be false.  Until such a producer is proved, nodes `[129]` and
`[131]` remain yellow against `original_erdos_64_proof.tex`.

The sequential review rows are therefore:

| Node | Exact predecessor | Original local output | Kernel-checked evidence | First missing obligation |
|---|---|---|---|---|
| `[129]` | `[128]`: the full selected excess-port family with declared local activation supports | `\(\mathcal A_0=\mathcal P_{\rm exc}\)` and a baseline family with `\(E_{\rm spine}\le C_E n\)` | the active-family equality and an empty CT15 family with exact full deficit | construct the nonempty independent baseline family and prove its linear deficit |
| `[131]` | the blocker-free output of `[130]` plus the node-`[129]` baseline | the original free-pair entropy sandwich | the exact free-pair enumeration and free-anchor token partition | node `[129]`'s linear-deficit family, followed by the mixed-independence/skeleton injection theorem on the identical pair schedule |

The free-anchor token partition does not discharge the second row: it bounds
free pairs only after a later token-cap argument and is not the entropy
sandwich asserted by the original cell.

Under exact predecessor provenance this blocks the complete descendant cone
`[130]`--`[144]`, even where a later local classifier is independently sound.
In particular, the current all-pair `D_25` decision at `[137]` is not the
original `D_all` decision: `D_all` subtracts the node-`[131]` free-pair entropy
allowance from the complete pair demand and then compares the remaining
blocked demand with the 36-row class capacity.  Consequently the current
`D_25` within/overload residuals do not provide the original incoming edges to
`[138]`--`[143]`.

The original local contract of `[136]` itself is now implemented as reusable
support: CT9 scans the actual blocked-pair subtype, assigns its canonical
capacity token, and partitions it both into the 24 realizable admitted roles
and into the literal 36-role manuscript table with the twelve impossible
profile/target rows empty.  The exact window, remainder-surplus, and primitive
token supplies are retained.  This does not make `[136]` green from node `[1]`
while `[129]` is missing; it means only that no additional node-local lemma is
needed there once the exact predecessor chain is restored.

## Nodes [21]--[24]: live-hot/cold window handoff

The original proof strategy uses the full
`c13 = 118.108581006...` live-hot window cost.  If the live package is not
available on enough windows, Chapter 1 routes the resulting linear cold family
through nodes `[145]`--`[157]`, ending in a target hit, target defect, declared
handoff, route-8 closure, or a target-complete compression contradicting
minimality.  There is no new three-way node between `[21]` and `[22]`.

There was also a separate numerical-certificate gap inside this same block.
The manuscript uses the decimal lower rate `118.108581006` at nodes
`[22]`--`[24]`, whereas the finite certificate stated in the appendix and
the original finite certificate proves only the rounding-free integer inequality
`2^118 * p13BarrierFlatProduct < p13BarrierSafeProduct`.  The latter does not
imply the printed density numerator `118108581006 / 10^9`.  This numerical
gap is now closed by `P13ExactWeightedRate`: a Lean-proved fixed-point
repeated-square checker verifies the exact rational lower rate from the same
two finite products in 34 bounded integer rows, without materializing the
equivalent gigantic power inequality.  The remaining hot-side gap is the
arithmetic conversion from the verified dependent product and fixed capacity
to the manuscript's normalized hot bound.

The live/cold classification defect is now repaired by a packing-order
compatible-extension ledger.  Hotness is relative to the exact aggregate
already retained: an accepted extension carries recoverable simultaneous
local choices, graph-response commutation, and an injective fixed-capacity
spine code.  Failure retains the identical prior aggregate and window as the
cold entry.  Hence a locally available but globally dependent package is
routed cold exactly as the proof prescribes.

After the cold branch is completely closed, no surviving counterexample has a
linear unpaid cold family.  The full live-hot contribution can then be used in
the original node-`[22]` state-count comparison, yielding node `[23]` or the
node-`[24]` density cap exactly as Chapter 1 prescribes.

This row stays open, and its web residual stays red, until the retained local
rate bounds are multiplied into the final dependent-product capacity and the
graph-owned same-window F2--F5 continuation, bounded-germ extraction, and all
G1/G2/G3 or finite-table consumers are proved in Lean.

The exact partition, aggregate-relative rejection provenance, and
node-[151]/[152] cold-mass payment are implemented and connected.  In
particular, the non-cubic sequential-cold
sublist injects into distinct surplus units, inherits node [21]'s exact
square-root budget, and the cubic sublist supplies exactly thirteen selected
branch-excess incidences per window.  The remaining blockers in this row are
the arithmetic theorem multiplying all retained local rate bounds into the
final dependent-product capacity and the graph-owned F2--F5/G1--G3 cold
closure after the verified literal F1 constructor; without these the strict
node-[23] overflow cannot be eliminated and
the node-[24] numerical cap cannot yet be produced unconditionally.

## Node [153]: cold-return F1 and the stage-major continuation

The paper's short-self-return argument says that one outside return of length
`ell` can be smeared over all thirteen window offsets, thereby testing every
length in `[ell, ell + 12]`.  The exact graph data do not imply that statement.
A fixed return corridor has fixed boundary attachments.  A cycle through the
anchor window is available only at an offset whose window vertex is actually
adjacent to the current return endpoint, and its window contribution is the
literal distance between those two attachment offsets.  The existence of one
return does not create attachment edges at the other twelve offsets.

The reviewed F1 predicate therefore scans, at one fixed corridor prefix, the
thirteen literal offsets in the order `0,...,12`.  An offset is positive only
when the current endpoint has the corresponding attachment edge and the
resulting cycle has power-of-two length.  The positive payload retains the
canonical first offset, the absence of every earlier offset, and the literal
simple cycle.

The production continuation is stage-major.  At each stored prefix it checks
F1 first, then F2, F3, and F4 at that same prefix.  Only after every prefix is
negative for F1--F4 may the runner construct the exhaustive F5 germ and pass
it to node [154].  The older global `stage x Fin 13` F1 scan is auxiliary: a
global prepass would incorrectly allow a later F1 to outrank an earlier F2.

The blanket interval-smearing conclusion remains open unless an earlier
producer proves the required family of attachment edges or a separate
accounting argument consumes the missing rows.  Node [153] also remains open.
Its first missing implementation is the graph-owned two-boundary semantic
producer that must construct, from the stored prefixes, either a
proof-selected compatible-context distinction for F2 or the universal
compatible-context equality and proper replacement required for F3.  The
exact Type-B/route-8 key for F4 and terminal/repeated-state germ for F5 must be
constructed downstream by the same producer chain.  No ambient context
universe may be enumerated.

## Node [144]: repeated routing code to sparse exit or Type-B handoff

The exact predecessor cone through nodes [125]--[143] is implemented.  It
constructs the activated surplus schedule, a repeated token/role fibre, a
literal matching-or-star homogeneous pattern, actual retained routing
supports, ordered-BFS germs, and the exhaustive prefix/cubic/high separator
classification.  This is all local polynomial computation on the supplied
pattern and supports.

The next prose implication in the original flow is not yet justified by those
payloads.  Three concrete gaps remain:

- unequal delayed selected-window attachment rows do not alone construct a
  target cycle or a named sparse-exit certificate (an induced path with two
  differently attached pendant leaves is a counterexample to that bare local
  implication);
- parallel or cubic-separated germs do not yet provide the common interface,
  target-response context, or certified smaller target-complete object needed
  by CT3/minimality;
- two compatible open high-centre ports do not yet provide the remainder
  support, carriers, marking, fan assignment, safety, and ledger provenance of
  the manuscript's decorated Type-B handoff.

Accordingly the existing `geometricResidual` is a sound prefix but not the
paper's promised node-[144] output.  Until a total local consumer constructs a
named sparse exit or a fully decorated Type-B entry on every residual leaf,
node [144] must remain non-green.  This blocks the fixed homogeneous caps and
the final contradiction of the strict node-[20] branch, but it does not weaken
the independently verified bounded-surplus field carried by node [21].

The first missing obligations are branch-specific but belong to the single
existing node `[144]` consumer; they are not new diagram cases:

| Exact retained leaf | Original required output | Missing producer data |
|---|---|---|
| first unequal attachment row | named sparse exit | a declared target-response coordinate or a literal return/cycle; one asymmetric adjacency is insufficient |
| aligned left/right prefix | sparse exit through defect/compression/delocalization | two same-interface boundaried pieces, a complete finite response table, and either a concrete distinguishing context or a certified smaller representative |
| cubic root/after-edge separator | sparse exit through the switch quotient | the actual switch representatives, reconstruction, compatible-context response semantics, and strict replacement rank decrease |
| high compatible separator | decorated Type-B handoff | a connected `P13`-free remainder core, terminal arms into that core, fan-safe first neighbours, and the four semantic predicates of the existing decorated-handoff edge |
| high open-endpoint failure | named blocker/exit | equality with selected active surplus slots; the BFS separator ports need not be selected ports |

In particular, the high leaf cannot be sent directly to the existing
`Exit7Handoff`: that type requires a connected negative support with no
internal high center and proof-carrying arms terminating in its counted core.
The node-`[144]` germ source retains two BFS tails and a high separator but no
such negative remainder core.  Filling those fields with caller predicates or
arbitrary `True` relations would restate the conclusion and is rejected by the
green-node audit.
