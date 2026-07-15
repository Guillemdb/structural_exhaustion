# Red-team audit: admitted whole-support quotient at nodes [43]--[46]

Verdict: **PASS**.

## Provenance

| Used fact | Producer | Earlier on path | Independent of repair |
|---|---|---:|---:|
| finite raw curvature coordinates | nodes [30]--[31] | yes | yes |
| admitted quotient and identified distinct coordinates | CT15 determination/rank-drop certificate | yes | yes |
| certified reduction when the admitted code is non-injective | `def:admissible-rank-quotient` | yes | yes |
| minimal-counterexample contradiction | CT2 minimality context | yes | yes |

No near-cubic estimate, entropy bound, later pressure theorem, or fact from a
sibling branch is used.

## Quantifier attack

- The central theorem is for one fixed finite response system, one fixed raw
  proposal, and a proof that this proposal is admissible.  It is not quantified
  over all graphs or all context completions.
- Injection is used only to rule out identification of two distinct declared
  coordinates.  It is not presented as surjectivity, simultaneous Boolean
  realization, or a full product-state theorem.
- The representative is not assumed unconditionally.  It is obtained only on
  the non-injective side by applying the conditional field already present in
  the admitted quotient.
- The smallest attempted countermodel is a two-coordinate constant code.  Such
  a raw proposal exists, but it cannot be an admitted quotient of a minimal
  counterexample unless its `representedReduction` field constructs the C2
  contradiction.  Thus it does not create a residual.

## Branch and CT audit

The branch table has two leaves: injective code contradicts the supplied
distinct identification (C5), while non-injective code invokes the certified
reduction and minimality (C2).  Both consume the exact predecessor payload.
There is no typed handoff, recursive return, or unconsumed leaf.  The CT15
execution still uses the explicit local coordinate enumeration and retains its
linear work theorem.

## TeX--Lean correspondence

- `CT15.AdmissibleQuotient.Admissible.injective` proves the generic minimality
  result.
- `Graph.ClosedRankDrop.ExactBarrier` and
  `Graph.ClosedRankDrop.rankDrop_impossible` expose the reusable whole-support
  interface without a global context audit.
- `P13WholeDelocalization` carries the concrete admitted quotient and literal
  distinct-coordinate identification from the Erd\H{o}s response system.
- `p13WholeDelocalization_impossible` closes node [46].
- `Graph.OneThreeRepair.Component.identity` is the separately reusable
  node-[44] graph theorem, with a Mantel `K_4` instantiation.

Searches found no `sorry`, `admit`, unsafe declaration, or new axiom in the
affected modules.  The only authorized external mathematical interface remains
the existing HSS theorem.  Focused framework, Erd\H{o}s, and Mantel builds must
pass before this verdict is reflected as green web coverage.
