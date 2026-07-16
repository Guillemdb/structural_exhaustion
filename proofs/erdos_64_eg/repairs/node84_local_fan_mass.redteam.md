# Independent-style red-team audit: repaired local node [84]

## Verdict

**PASS for the narrowed local node `[84]`; FAIL/open for the separated global
ordinary/grouped coefficient-208 aggregate.**  These are different nodes after
the contract split and no theorem routes the local PASS into the global claim.

## Quantifiers and provenance

- The local theorem quantifies over one exact selected minimal-counterexample
  context, one literal `TypeBSupportScope`, and the `NoHigherCenter` branch.
- Its route is obtained by executing `degreeFourB2Route`, whose four
  constructors are the exhaustive node-`[81]`--`[83]` output.
- The unresolved constructor opens the exact existential and retains the
  proof that this center has no verified local entry.
- The overlap constructor retains the exact `resolution` and exact CT12
  `MinimalOverlap`; its center set is `obstruction.selected.toFinset`.
- No family of supports, canonical decomposition, grouped envelope, or
  coefficient theorem appears in the local input or conclusion.

## Both-sides and branch-total audit

| Incoming outcome | Repaired output | Terminal/consumer | Status |
|---|---|---|---|
| unresolved local entry | singleton selected-center CT14 mass | local capacity residual | closed locally |
| B2 nonnegative | identical `B2Nonnegative` | existing nonnegative closure | retained exactly |
| negative remaining core | identical `B2RemainingNegative` | existing route-8 consumer | retained exactly |
| minimal overlap | exact selected-list center set and CT14 mass | local capacity residual plus same overlap | closed locally, obstruction retained |

CT14's unbounded and missing-label branches are impossible definitionally:
every actual center receives `some capacity` and `some label`.  Its aggregate
branch is impossible because `1 <= degree-3` is proved pointwise.  Therefore
the unique execution is the capacity branch and all CT14 terminals are
accounted for.

## Injection, realization, and duplicate audit

The local proof requires no map from support occurrences to role--center
tokens.  For overlap centers, the selected list is a sublist of the exact
duplicate-free `FinEnum.orderedValues` schedule.  Lean proves the sublist is
`Nodup`, hence `selected.toFinset.card = selected.length`.  This is an exact
realization of the obstruction's centers, not an injection substituted for a
global grouped-family theorem.

The earlier countermodel with two identical support scopes still refutes the
global within-role claim.  It does not refute the narrowed local theorem,
which quantifies over one scope and never aggregates scopes.

## Computation and trust audit

- Local data scanned: only `scope.centers`, derived by filtering the supplied
  literal core vertex schedule for degree at least four.
- Per center: one selected-membership test and the already computed ambient
  degree surplus.
- Exact generic ledger: `4 * scope.centers.card + 1` profile-operator calls.
  The application does not pretend list-backed finite-set membership is
  constant-time: its expanded comparison ledger is
  `4 * scope.centers.card * (selected.card + 1) + 1`, formally bounded by
  `5 * (scope.centers.card + 1)^2`.
- Forbidden enumeration: no graph family, vertex powerset, support family,
  candidate product, path family, or subgraph family is evaluated.
- `#print axioms` for the generic stage and local route reports only standard
  Lean axioms.  The existential prefix additionally reports the repository's
  sole allowed Hegde--Sandeep--Shashank theorem, inherited through the exact
  predecessor chain.

## Global-frontier non-circularity audit

`TypeBGlobalFanMassProducer` contains the still-required support-indexed
profile and coefficient equality.  There is no function from
`VerifiedTypeBLocalFanMassPrefix` to this producer.  The theorem producing the
factor-416 bound explicitly requires an inhabitant of the downstream producer
type.  Consequently:

- local node `[84]` does not assume coefficient `208`;
- local node `[84]` does not assume ordinary/grouped incidence disjointness;
- local node `[84]` does not cite the factor-416 theorem;
- the global theorem cannot be used until its missing producer is actually
  constructed and red-teamed.

## Commands

```text
cd lean
lake build StructuralExhaustion.Graph.SelectedSurplusMass \
  StructuralExhaustion.Examples.SelectedSurplusMass
  passed

cd examples/erdos_64_eg
lake build Erdos64EG.CT14TypeBLocalFanMass
  passed

lake env lean /tmp/check_node84.lean
  local generic/route: standard Lean axioms only
  existential prefix: standard Lean axioms plus sole HSS theorem
```

## Integration gate

The local code is PASS-ready for later TeX--Lean--web synchronization as a
contract repair.  The original manuscript sentence `M_B <= 416 sigma(G)` must
not remain attached to this local node.  It must be redirected to the new
downstream global producer/aggregate frontier and remain non-green until the
canonical family, incidence components, and both coefficient-208 semantic
bounds are proved.
