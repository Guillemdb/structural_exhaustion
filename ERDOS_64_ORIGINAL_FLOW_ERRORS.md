# Erdős--Gyárfás 64 original-flow repair register

## Nodes [21]--[24]: live-hot/cold window handoff

The original proof strategy uses the full
`c13 = 118.108581006...` live-hot window cost.  If the live package is not
available on enough windows, Chapter 1 routes the resulting linear cold family
through nodes `[145]`--`[157]`, ending in a target hit, target defect, declared
handoff, route-8 closure, or a target-complete compression contradicting
minimality.  There is no new three-way node between `[21]` and `[22]`.

The current formal gap is the paper's own live/cold interface.  The statement
of `lem:p13-window-package` asserts the full package for every packed window,
while `def:cold-window-ledger` and the proof of
`thm:cold-branch-quantitative-closure` require a possibly nonempty family of
windows on which that package is not live.  The formalization must define this
partition canonically and prove that every non-live window enters the exact
same-window cold corridor ledger.

After the cold branch is completely closed, no surviving counterexample has a
linear unpaid cold family.  The full live-hot contribution can then be used in
the original node-`[22]` state-count comparison, yielding node `[23]` or the
node-`[24]` density cap exactly as Chapter 1 prescribes.

This row stays open, and its web residual stays red, until the live-package
predicate, hot/cold partition, cold-mass inequality, same-window F1--F5
connector, bounded-germ extraction, and all G1/G2/G3 or finite-table consumers
are proved in Lean.
