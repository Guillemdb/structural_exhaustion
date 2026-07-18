# Erdős 64 nodes [85]–[128]: obligation and predecessor ledger

Authority: `original_erdos_64_proof.tex`.  This ledger records the immutable
Chapter 1 topology.  It does not add a node, edge, outcome, or assumption.
Statuses refer to unconditional, same-context Lean provenance on 2026-07-17.
`Proved-local` means the stated local lemma exists, but the node is not green
unless every row is proved and its exact predecessor is green.

## Dependency summary

- Node [85] consumes the two original inputs [82] and [84].  Its earliest
  unavailable predecessor is [84].
- The Type-A flow [86]–[124] consumes the no-high-center output [63].  Local
  support, receiver, path, and response machinery exists, but no unconditional
  endpoint executes the complete receiver split and all eight exits from the
  canonical [61] support.  The first local missing producer is the [89]
  saturation split with its exact [93] visible-four or [94] silent residual.
- Part X [125]–[128] is an independent continuation of [20], not a successor of
  [124].  The strict scale residual is preserved, but [125] lacks the paper's
  additional assertion that all named sparse exits have been tested and are
  absent.  Therefore [125]–[128] must all be yellow under the green-predecessor
  rule.  Their proved arithmetic and activation tasks remain recorded below.

## Node [85] — degree-four Type-B closure

| Task ID | Original-paper obligation/property | Exact predecessor | Lean evidence | Status | Missing producer |
|---|---|---|---|---|---|
| N85-PROV-82 | Retain the certificate-closed/B2-paid branch and its nonnegative net charge. | [82] | Degree-four local ledger modules | partial | Exact [82] public residual into [85] |
| N85-PROV-84 | Retain the grouped fan-mass residual on the same selected centers. | [84] | Type-B fan-mass modules | missing | Green [84] grouped fan-mass output |
| N85-SUBLIN | Prove the fan-certificate/B2-failure residual is sublinear from assigned surplus. | [84] | No unconditional same-context endpoint | missing | [84] global fan-mass bound |
| N85-CLOSE | Deduce degree-four Type B cannot carry linear deficit outside route 8. | both inputs | No unconditional endpoint | missing | N85-PROV-84 and N85-SUBLIN |
| N85-OUT | Preserve the route-8 core as the sole original outgoing residual. | [85] | Typed Type-B residual interfaces exist | partial | N85-CLOSE |

## Nodes [86]–[94] — Type-A support and receiver split

| Task ID | Node | Original-paper obligation/property | Exact predecessor | Current evidence | Status | Missing producer |
|---|---:|---|---|---|---|---|
| N86-PROV | 86 | Consume the exact no-high-center connected negative support. | [63] | `TypeANode63Support.VerifiedNode63Residual` | partial | Green [63] endpoint from canonical [61] localization |
| N86-CUBIC | 86 | From `sigma(X)=0`, prove every support vertex has ambient degree 3 and the induced support is subcubic. | [63] | `ambientDegree_eq_three_of_noHigh`, `support_degree_le_three_of_noHigh` | proved-local | Green predecessor |
| N86-DEF | 86 | Convert negative net charge to `def(X)<|X|/4` and average degree `>2.75`. | [61],[63] | Quarter-charge structures retain negativity | partial | Explicit theorem with the paper's `def` and cardinality formula |
| N86-INHERIT | 86 | Retain connectedness, admissibility, contextual dyadic safety, empty internal 3-core, P13-freeness, supplied deficiency, and hereditary uncompressibility. | [61],[63] | P13-free, target-free, HSS core-free proved; other predicates remain interfaces | partial | Concrete admissibility/uncompressibility bridge |
| N87-P13 | 87 | Prove the exact support is induced-P13-free. | [86] | `support_p13Free` | proved-local | Green [86] |
| N87-DIAM | 87 | Deduce diameter at most 11 from shortest paths being induced. | [86] | No exact Type-A endpoint | missing | Local shortest-path lemma on `supportObject` |
| N87-CARD | 87 | Execute the subcubic BFS bound `|X|<=6142` (and root-degree-two refinement `<=4095`). | [87] | No exact Type-A endpoint | missing | Local BFS-layer cardinality theorem |
| N88-Q | 88 | Define receivers, completion ports, `q(w)=3-d_X(w)`, traces, `r(u)`, and loads `L(w)` on the exact support. | [87] | Graph Type-A canonical receiver/trace and completion-port modules | partial | Bundle all paper objects in one [88] residual |
| N88-UNIQUE | 88 | Prove every cubic support vertex is routed to exactly one receiver by the canonical trace. | [88] | Graph canonical receiver trace API | proved-local | Exact [88] wrapper |
| N88-THRESH | 88 | Prove `H_j=4(j+1)`, hence thresholds 4, 8, 12 and residual capacities 3, 7, 11. | [88] | `Graph.TypeAReceiverSaturation` arithmetic | proved-local | Exact [88] wrapper |
| N89-DECIDE | 89 | Decide on the actual finite receiver set whether some `L(w)>=4q(w)`. | [88] | Receiver-saturation reusable scan exists | partial | Execute it on canonical [88] schedule and retain witness/no-witness |
| N89-YES | 89 | On yes, retain the same receiver, its load, ports, traces, and saturation proof for [93]. | [89] | No complete public residual | missing | Canonical saturation witness producer |
| N89-NO | 89 | On no, prove every receiver has `L(w)<=4q(w)-1` for [90]. | [89] | Arithmetic implication exists | partial | Exhaustive finite scan result |
| N90-BOUND | 90 | State the unsaturated 3/7/11 per-receiver bounds on the same routed-load partition. | [89] no | Threshold arithmetic exists | partial | N89-NO |
| N90-PART | 90 | Retain that every cubic vertex is charged exactly once to a receiver. | [88] | Canonical trace uniqueness | proved-local | Green [88] |
| N91-CHARGE | 91 | Sum receiver charges and routed cubic costs to prove `11n0+7n1+3n2>=n3`. | [90] | No unconditional exact-support sum theorem | missing | Finite receiver/load partition summation |
| N91-DENS | 91 | Convert the charge inequality to `def(X)>=|X|/4`, equivalently average degree at most 2.75. | [91] | Arithmetic not exposed as exact node theorem | missing | N91-CHARGE plus support degree sum |
| N92-CLOSE | 92 | Contradict the node-[86] strict deficiency inequality on the unsaturated branch. | [91] | No endpoint | missing | N91-DENS and exact [86] negativity |
| N93-VISIBLE-DECIDE | 93 | On the exact saturated receiver, scan actual completion ports and decide whether one carries four distinct visible unpeeled receiver-entry returns. | [89] yes | `TypeANode93VisibleFamily.VerifiedNode93Residual` is a payload type only | missing | Producer from the canonical saturated receiver and visible schedule |
| N93-YES | 93 | Retain one actual port and the first four visible, distinct, unpeeled returns with traces/channels/response coordinates. | [93] yes | `node95Input`, `node95Family`, distinct/unpeeled/visible lemmas | proved-local | N93-VISIBLE-DECIDE |
| N93-NO | 93 | Prove every port has at most three visible returns and retain the silent excess ledger. | [93] no | No exact residual | missing | Exhaustive port scan |
| N94-EXCESS | 94 | Prove `S_sil^exc(X)>=4D_A(X)` from saturation and failure of visible-four. | [93] no | Silent-basin support machinery is partial | missing | N93-NO plus no-overcount summation |
| N94-OUT | 94 | Route the silent residual unchanged to exit (4) testing. | [94] | No exact edge payload | missing | N94-EXCESS residual |

## Nodes [95]–[109] — the eight original saturated exits

| Task ID | Node | Original-paper obligation/property | Exact predecessor | Current evidence | Status | Missing producer |
|---|---:|---|---|---|---|---|
| N95-TEST | 95 | Test the four actual node-[93] returns for a Mersenne return. | [93] yes | `node95_exit1_closed` proves one stored return is not Mersenne; no four-entry runner | partial | N93-YES and finite four-entry test |
| N95-NO | 95 | Retain all four returns and their non-Mersenne facts for [97]. | [95] no | Per-channel spectral theorem | partial | Four-entry aggregation |
| N96-CYCLE | 96 | Convert a Mersenne return plus the completion edge into a power-of-two cycle in the same graph. | [95] yes | Receiver-entry spectral/target bridge | proved-local | N95 yes witness |
| N97-TEST | 97 | Test actual pairs for internally disjoint common-port returns whose lengths sum to a power of two. | [95] no | `TypeAExit2CommonPort.Exit2` | partial | Pair schedule over exact four returns |
| N97-NO | 97 | Retain failure of exit 2 for every tested pair. | [97] no | No exhaustive residual | missing | Pair runner/trace |
| N98-CYCLE | 98 | Build the simple union cycle and prove its target length. | [97] yes | `TypeAExit2CommonPort.cycle`, `.closes` | proved-local | N97 yes witness |
| N99-TEST | 99 | Test same-window P13 labels of the four trace/return coordinates for the required `C_s` collision. | [97] no | P13 label algebra exists globally | missing | Projection of actual four returns to their packed-window labels |
| N99-NO | 99 | Retain all required legal-label relations for [101] and [107]. | [99] no | No exact residual | missing | N99 exhaustive runner |
| N100-CLOSE | 100 | Turn the failed `C_s` relation into the stated label/target collision. | [99] yes | P13 label cycle constructors exist | partial | Actual Type-A trace-label connector |
| N101-COMPARE | 101 | Build the finite declared-code comparison on the same unpeeled load/support and execute the target-defect test. | [99] no or [94] | `TypeAExits4To6Semantics.Comparison.run` | partial | Concrete comparison, code coverage, and neutral-location producer |
| N101-YES | 101 | Produce the literal target-defective quotient with its supported routed load. | [101] yes | `Exit4`, target-defect route | partial | N101-COMPARE on exact Type-A data |
| N101-NO | 101 | Retain target-completeness of the response equality for [103]. | [101] no | Generic neutrality result | partial | Concrete comparison producer |
| N102-PEEL | 102 | Remove exactly one target-defective routed load and account exactly one quarter unit of receiver charge. | [101] yes | Exit-4 semantic type exists | missing | Canonical peel operation and exact load/charge theorem |
| N102-DESCENT | 102 | Prove the finite potential `Lambda_4` strictly decreases and recompute `L_4` before returning to [89]. | [102] | No exact implementation | missing | Peeling schedule and well-founded descent |
| N103-TEST | 103 | Test whether the neutral equality is a nontrivial target-complete smaller proper representative. | [101] no | `NeutralLocation.atAtom` and `Exit5` | partial | Concrete atom/location producer |
| N103-NO | 103 | Retain failure of proper compression for [105]. | [103] no | No exact residual | missing | Exhaustive response classification |
| N104-CLOSE | 104 | Contradict hereditary target-uncompressibility from the exact compression. | [103] yes | `Exit5.closes` | proved-local | N103 yes witness from exact predecessor |
| N105-TEST | 105 | Classify the remaining neutral equality as proper or global delocalization. | [103] no | `NeutralLocation.delocalized`, `Exit6.routed` | partial | Concrete enlarged-support location producer |
| N105-NO | 105 | Retain failure of delocalization for [107]. | [105] no | No exact residual | missing | Exhaustive location result |
| N106-CLOSE | 106 | Close the proper/global delocalization branch using the existing smearing results. | [105] yes | Delocalization route type exists | partial | Concrete link to proper/global closure theorem |
| N107-SEPARATOR | 107 | From failure of exits 4–6, select the actual first surviving connector separator. | [105] no | Local family classifier can return an actual separator | partial | N93/N94 exact family and absorbed-outcome connection |
| N107-HIGH | 107 | Prove a degree-3 separator is absorbed by exits 4–6, hence the survivor has degree at least 4. | [107] | `VerifiedNode107Residual` currently accepts absorption as a field; `center_high` only consumes it | missing | Derive cubic-switch absorption from `TypeAExits4To6Semantics.run` |
| N107-FANSAFE | 107 | Prove every selected first-neighbour pair satisfies all five fan-safe clauses; each failure routes to exits 2–6. | [107] | `fan_failure_absorbed` is caller-supplied | missing | Clause-by-clause failure routing from prior no-exit residuals |
| N107-INHERIT | 107 | Retain contextual safety, P13-free empty-core core, uncompressibility, arms, and first-entry facts. | [86]–[107] | Arms/first-entry graph lemmas; semantic predicates are fields | partial | Concrete predicate bridges |
| N108-BUILD | 108 | Construct the decorated Type-B handoff fan with the same counted core, high center, actual arms, and fan-safe neighbour clique. | [107] yes | `VerifiedNode107Residual.node108` | proved-local | Green [107] |
| N108-ADMISS | 108 | Prove the handoff carries exactly the Type-B contextual safety, P13-free/core-free, uncompressibility, and fan-return data. | [107] | Constructor preserves supplied predicates | partial | N107-INHERIT from concrete graph semantics |
| N108-EDGE | 108 | Route definitionally to the existing dashed [66] input without changing support or graph. | [108] | `TypeBEntryRouting.node66`, source/data simp theorems | proved-local | Green [108] |
| N109-RESIDUAL | 109 | If exit 7 also fails, retain exactly exit (8): the silent route-8 residual with every absent-exit constraint. | [107] no | Manuscript-facing types exist only partially | missing | Complete sequential exit runner and survivor constructor |

## Nodes [110]–[124] — route-8 pressure closure

| Task ID | Node | Original-paper obligation/property | Exact predecessor | Status | Missing producer |
|---|---:|---|---|---|---|
| N110-PROFILE | 110 | Define the true route-8 residual: saturated silent basin, declared `u`-supported response algebra, and absence of exits 1–7. | [109] | missing | N109-RESIDUAL |
| N110-CARRIERS | 110 | Define essential/private carriers and target-complete carrier cores on the exact residual. | [110] | partial | Concrete graph producer rather than author contract |
| N111-EXTRACT | 111 | The global squeeze selects a finite collection `X_A` of true route-8 entries carrying the entire residual Type-A deficit. | [110] plus global budgets | missing | Same-graph extraction/no-loss theorem |
| N111-NOCOUNT | 111 | Prove supports/loads are counted with the manuscript multiplicities and Type-B mass is excluded. | [85],[111] | missing | Green [85] and pressure no-overcount ledger |
| N112-BURDEN | 112 | Prove `N_basin(X_A)>=4 D_A(X_A)`. | [111] | missing | Aggregate silent-excess theorem |
| N113-DEFICIT | 113 | Prove `D_A(X_A)>=(1/4-tau_win)|R|-o(|R|)` from the large-budget global squeeze. | [111], window budget | missing | Exact asymptotic handoff on same graph |
| N114-CORE | 114 | For each indexed entry choose the canonical minimal target-complete carrier core inside the declared supported response algebra. | [110]–[113] | missing | Existence, minimality, and canonicity theorem |
| N114-PRESERVE | 114 | Preserve entry, basin, deficit, absent exits, and carrier incidence under core restriction. | [114] | missing | Carrier restriction bridge |
| N115-DECIDE | 115 | Decide on the actual finite entry collection whether some `alpha_X(xi)<=1`. | [114] | missing | Local finite carrier-count scan |
| N115-NO | 115 | On no, retain `alpha>=2` for every entry for [117]. | [115] no | missing | Exhaustive scan residual |
| N116-CLOSE | 116 | Show a zero/one-essential-core entry realizes one of original exits 4–7. | [115] yes | missing | Carrier-to-exit classification |
| N117-DECIDE | 117 | Decide whether some entry has at most two private essential carriers `pi_X(xi)<=2`. | [115] no | missing | Actual finite private-carrier scan |
| N117-NO | 117 | On no, retain at least three private essential carriers for every indexed entry. | [117] no | missing | Exhaustive scan residual |
| N118-RESIDUAL | 118 | On yes, retain the exact two-carrier true route-8 entry and all absent-exit/deletion data for [123]. | [117] yes | partial | Concrete producer from canonical carrier ledger |
| N119-PRIVATE | 119 | State and prove every indexed entry has at least three private essential carriers. | [117] no | missing | N117-NO |
| N120-INJECT | 120 | Prove private carriers are charged with the manuscript multiplicity/no-overcount rule. | [119] | missing | Private-carrier injection/capacity lemma |
| N120-UPPER | 120 | Derive `3N_basin<=def(R)+o(|R|)<=tau_win|R|+o(|R|)`. | [119] plus density cap | missing | N120-INJECT and green quantitative window bound |
| N121-LOWER | 121 | Combine [112] and [113] to derive `N_basin>=4(1/4-tau_win)|R|-o(|R|)`. | [112],[113] | missing | Green predecessors and asymptotic algebra |
| N122-COMBINE | 122 | Combine [120] and [121] to force `tau_win>=12(1/4-tau_win)`. | [120],[121] | missing | Same-scale little-o elimination |
| N122-NUM | 122 | Prove this contradicts the paper's strict `tau_win<3/13`. | [122] | partial | Fixed rational arithmetic after N122-COMBINE |
| N123-LEDGER | 123 | Join the remaining large-budget target-defect/route-8 ledger after Type-B mass removal. | [85],[118] | missing | Green [85] and concrete [118] |
| N123-PEEL | 123 | Every target-defect entry is a canonical exit-4 peel that strictly decreases `Lambda_4`. | [123] | missing | Exact exit-4 descent theorem |
| N123-TERM | 123 | Finite descent terminates; the only nonpeeling survivor is the terminal true route-8 obstruction. | [123] | missing | Well-founded finite descent |
| N124-WITNESS | 124 | Every essential carrier has the declared deletion witness required by the paper. | [123] | missing | Witness producer from minimality/response algebra |
| N124-CANON | 124 | For a two-carrier entry, those deletion quotients are canonical exit-4 quotients. | [124] | missing | Carrier-deletion canonicality theorem |
| N124-EXIT | 124 | Each quotient realizes exit 4, contradicting its absence in a true route-8 residual. | [124] | missing | Exact exit-4 semantic connector |
| N124-CLOSE | 124 | Conclude no terminal two-carrier route-8 obstruction exists. | [124] | missing | N124-WITNESS/CANON/EXIT |

## Nodes [125]–[128] — independent Part-X entry

| Task ID | Node | Original-paper obligation/property | Exact predecessor | Current evidence | Status | Missing producer |
|---|---:|---|---|---|---|---|
| N125-PROV | 125 | Retain the literal node-[20] strict non-near-cubic scale residual and identical node-[18] selected graph/label algebra. | [20] | `SparsePressureEntryResidual`, `routeSurplusScale` | proved | — |
| N125-LABEL | 125 | The selected graph has passed the finite P13 label algebra used by this branch. | [18],[20] | Nested `VerifiedP13LabelAlgebraPrefix` | proved | — |
| N125-EXITS-DEFINE | 125 | Define the five named sparse-exit families on actual selected demands, selected pairs, and baseline coordinates. | [20] | Paper definition has no complete Lean semantic counterpart | missing | Concrete exit predicates and finite schedules |
| N125-EXITS-RUN | 125 | Execute the original sparse-exit tests locally and exhaustively, retaining either an existing exit edge or the survivor branch. | [20] | No runner/residual | missing | Local demand/pair/baseline test runner |
| N125-SURVIVE | 125 | On the Part-X edge, prove none of the named sparse exits occurs for any scheduled coordinate. | [125] survivor | No field in `SparsePressureEntryResidual` | missing | N125-EXITS-RUN survivor payload |
| N125-WORK | 125 | Bound the actual local exit schedule polynomially without graph/context enumeration. | [125] | Scale decision alone is constant work | partial | Work bound for N125-EXITS-RUN |
| N126-PROV | 126 | Consume the exact [125] survivor on the same graph. | [125] | `VerifiedSparseEnvelopeFromPressure` preserves only the strict residual | partial | N125-SURVIVE field |
| N126-EDGE | 126 | Prove `m<=2n-2`. | [125] | `sparseEnvelope_edgeBound` | proved-local | Green [125] |
| N126-SLACK | 126 | Define `lambda=2n-3-m`, `sigma=2m-3n` and prove `sigma=n-6-2lambda`. | [126] | `sparseSlack`, `sparseSurplus`, `sparseSlack_surplus_identity` | proved-local | Green [125] |
| N126-SECOND | 126 | Prove the equivalent division-free edge/surplus identity. | [126] | `sparseEdge_surplus_identity` | proved-local | Green [125] |
| N126-RUN | 126 | Execute the actual local CT12 peeling certificate with trace, validity, totality, iterations, and linear work bound. | [126] | `runSparseEnvelopeCT12_*` | proved-local | Green [125] |
| N127-PROV | 127 | Consume the exact [126] output while retaining [125]/[20]. | [126] | `VerifiedSurplusPortActivationFromPressure` | proved-local | Green [125]/[126] |
| N127-SELECT | 127 | Define the actual excess selector: exactly `d(h)-3` incident ports per high center. | [126] | Graph surplus-port slot schedule | proved-local | Green predecessor |
| N127-CARD | 127 | Prove `A=P_exc` and `|A|=sigma(G)`. | [127] | `activatedSurplusSchedule_length_eq_sigma`, surplus/ledger identity | proved-local | Green predecessor and survivor condition |
| N127-ENDPOINT | 127 | For every selected `(h,x)`, prove `d(h)>=4`, `d(x)=3`, and `N(x)={h,a_p,b_p}` with distinct shoulders. | [127] | Graph `ActiveDemand` supplies port support/cubic endpoint data | proved-local | Green predecessor |
| N127-WORK | 127 | Scan only the actual vertex/slot schedule with a polynomial bound. | [127] | CT6 linear/quadratic check theorems | proved-local | Green predecessor |
| N128-PROV | 128 | Consume the identical [127] selected slot family and same graph. | [127] | `VerifiedSurplusPortActivationPrefix`; pressure wrapper preserves context | proved-local | Green [127] |
| N128-RETURN | 128 | Canonically choose a simple `x`–`h` return `R_p` in `G-hx`, first edge through one shoulder. | [127] | `Graph.SurplusPortActivation.ActiveDemand` | proved-local | Green predecessor |
| N128-OPEN | 128 | In the open case, produce canonical `Q_p` in `G-x` with length `2^j-1`, `j>=2`, from suppression/minimality. | [128] | `activatedSurplusStage`, `openResponse_has_mersenne_length` | proved-local | Green predecessor |
| N128-TRI | 128 | In the triangular case, retain the triangle and canonical return. | [128] | Graph activation verified stage | proved-local | Green predecessor |
| N128-CANON | 128 | Prove all response data are canonical functions of the selected graph order and port, with no caller witness. | [128] | `verifiedActivatedStageFromMinimality` | proved-local | Green predecessor |
| N128-WORK | 128 | Account only for actual selected slots/paths; never enumerate ambient graphs or contexts. | [128] | Graph activation schedule and prior CT6 bounds | partial | Explicit combined activation work theorem |

## Required status correction

- Promote: none.
- Demote from green: [125], [126], [127], [128].
- Preserve as proved obligations despite demotion: N125-PROV, N125-LABEL;
  N126-EDGE/SLACK/SECOND/RUN; N127-PROV/SELECT/CARD/ENDPOINT/WORK; and
  N128-PROV/RETURN/OPEN/TRI/CANON.
- First repair target on this independent branch: N125-EXITS-DEFINE, then
  N125-EXITS-RUN, N125-SURVIVE, and N125-WORK.  Only after those four tasks are
  kernel-checked may [125] be green; [126]–[128] can then be reconsidered in
  order without redoing their existing local proofs.

