# Repair sketch: sequential P13 hot/cold ledger

Process the exact duplicate-free packing in its canonical list order.  The
state is one retained jointly compatible aggregate.  At window `W`, test the
local proposition `Nonempty (Extension aggregate W)`.  On success choose that
extension, append `W` to hot, and replace the aggregate by the extended valid
aggregate.  On failure append the identical `W` to cold and keep the aggregate
unchanged.  Thus rejection is the paper's cold branch, not a third outcome.

The reusable runner is implemented in
`StructuralExhaustion.Core.SequentialCompatibleExtensionLedger`.  Its ledger
is indexed by the current aggregate, so the tail of a hot step can only start
at the aggregate produced by that step.  It proves exact hot/cold partition,
sublist provenance, nodup, final aggregate validity, and one compatibility
decision per supplied window.  It scans neither graphs nor contexts;
construction and checking of `Extension` remain application-owned local
semantic producers.  A non-Erdos transfer is in
`StructuralExhaustion.Examples.SequentialCompatibleExtensionLedger`.

For Erdős, `Extension aggregate W` must mean an actual graph-owned extension
of the retained hot aggregate, with response commutation and recoverable
skeleton semantics.  A faithful application needs the following lemmas/data.

1. `originalGlobalCompletion`: interpret `ctx.G` as the empty aggregate's
   `P13Node160GlobalGraphCompletion` for every selected packed window.
2. `localInterpretation`: turn a proposed live package for `W` into a
   `P13WeightedLocalGraphInterpretation package`, or reject that proposal.
3. `extendGlobal`: given the current global completion and the interpreted
   package, produce a new global completion.
4. `oldResponsePreserved`: the new completion has exactly the old responses
   for every already retained package/state/coordinate.
5. `newResponseCommutes`: the response of every state/coordinate in the new
   package agrees between its local interpretation and the new global
   completion.
6. `recoverRetained`: restricting the new global completion to each retained
   owner recovers its previous local completion data.

The strengthened application contract is implemented in
`Erdos64EG.P13SequentialWeightedHotColdLedger`.  A hot aggregate now owns a
finite joint-state family, recoverable glue from the dependent product of all
retained local state families, a graph completion for every joint state,
response commutation, and an injective finite skeleton code with a fixed
baseline-spine capacity.  The generic dependent-owner theorem derives the
local-product capacity bound.  Items 1--6 above are fields of the aggregate or
of the *extension type*, not assumptions of the runner.  Consequently failure
of any item is exactly the cold branch.

There is also a concrete public-type correction.  The present
`P13WeightedColdWindow.packageAbsent` asserts absence of a one-window live
package.  Sequential rejection instead asserts absence of a compatible
extension of the current aggregate.  A locally live but globally incompatible
window is cold in the manuscript.  No downstream consumer reads
`packageAbsent`, so the record can be replaced by the rejection aggregate,
its validity proof, and `extensionAbsent` once the semantic types are moved
below `P13WeightedHotColdInterface`.  At present
The corrected implementation therefore lives in a higher module importing
both the old one-window package interface and its graph interpretation, which
avoids that import cycle.  Downstream cold geometry must consume
`p13SequentialWeightedColdWindows`; consumers that still mention
`p13WeightedColdWindows` remain connected to the obsolete isolated split.
