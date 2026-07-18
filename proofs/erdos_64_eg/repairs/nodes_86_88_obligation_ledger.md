# Original nodes [86]--[88] obligation ledger

This ledger follows the unique manuscript chain `[63] -> [86] -> [87] -> [88]
-> [89]`.  It records the complete obligation set of each cell; in particular,
the missing node-[87] Moore-bound producer is not hidden inside node [88].

## Node [86]

| Task | Original-paper obligation | Lean evidence | Status |
|---|---|---|---|
| VIII-86-01 | Consume the identical no-high Type-A support from node [63]. | `VerifiedNode86Residual.previous`, `exactPrevious`, `profile_support`. | proved |
| VIII-86-02 | Retain the localized strict negative net charge. | `negativeNetQuarter`, projected by `node86` from node [61]. | proved |
| VIII-86-03 | Prove `sigma(X)=0` on this support. | `VerifiedNode86Residual.assignedSurplus_eq_zero`. | proved |
| VIII-86-04 | Derive `4 def^+(X) < |X|`. | `VerifiedNode86Residual.four_deficiency_lt_card`. | proved |
| VIII-86-05 | Perform no new graph-family search. | `node86` is a constant-work projection. | proved |

Node [86] has 5/5 obligations implemented.

## Node [87]

| Task | Original-paper obligation | Lean evidence | Status |
|---|---|---|---|
| VIII-87-01 | Consume the exact node-[86] residual. | `node87`; mandatory `previous` and `exactPrevious` fields. | proved |
| VIII-87-02 | Prove the identical induced support is `P13`-free. | `node87_p13Free`, from the maximum-packing remainder inclusion. | proved |
| VIII-87-03 | Prove every two support vertices have an internal simple path of length at most 11. | `InducedPathDiameter.diameterAtMostEleven_of_p13Free`; `node87_diameterAtMostEleven`. | proved |
| VIII-87-04 | Apply the subcubic breadth-first Moore count to prove `|X| <= 6142`. | `OrderedBFSTree.Profile.card_vertices_le_6142_of_radius_eleven`; `node87_supportCardAtMost6142_of_diameter`. | proved |
| VIII-87-05 | Use only one rooted finite BFS/layer schedule, never enumerate graphs or vertex universes. | `SubcubicMooreBound` scans the declared support layers and fresh-neighbour fibres; `InducedPathDiameter` uses one proof-selected shortest path; `node87Checks_polynomial` proves the local quadratic envelope. | proved |

Node [87] has 5/5 obligations implemented.  The total producer `node87`
closes the exact `[86] -> [87]` handoff.

## Node [88]

| Task | Original-paper obligation | Lean evidence | Status |
|---|---|---|---|
| VIII-88-01 | Consume a complete exact node-[87] residual. | `VerifiedNode88Residual.previous`, `exactPrevious`; `node88` accepts only `VerifiedNode87Residual`. | proved |
| VIII-88-02 | Define `q(w)=3-d_X(w)` on the identical support. | `q`. | proved |
| VIII-88-03 | Define the first saturated load `H(w)=4q(w)`. | `threshold`. | proved |
| VIII-88-04 | For `d_X(w)=2-j`, prove `H_j=4(j+1)`. | `classThreshold`. | proved |
| VIII-88-05 | Prove the displayed raw bounds `H0<=4`, `H1<=8`, `H2<=12`. | `H0_le_four`, `H1_le_eight`, `H2_le_twelve`. | proved |
| VIII-88-06 | Route only to the existing node [89], with constant local arithmetic work. | `node88`; `node88Checks_constant`. | proved |

Node [88] has 6/6 obligations implemented, and its exact predecessor node
[87] is now constructible by `node87`.
