import type { ExampleManuscript, GraphElement } from "./types";

export type ErdosProofNodeKind = "assertion" | "decision" | "terminal";

export interface ErdosProofNode {
  nodeId: number;
  kind: ErdosProofNodeKind;
  label: string;
}

export interface ErdosProofEdge {
  source: number;
  target: number;
  label?: string;
  dashed?: boolean;
}

export interface ErdosProofContinuation {
  source: number;
  target: number;
  label: string;
}

export interface ErdosProofPart {
  part: number;
  roman: string;
  title: string;
  summary: string;
  nodes: ErdosProofNode[];
  edges: ErdosProofEdge[];
  continuations: ErdosProofContinuation[];
}

// The immutable Chapter 1 topology is exactly the contiguous node range
// [1]--[157]. Formalization support declarations attach to those nodes; they
// never create supplemental proof-flow boxes or edges.
export const ORIGINAL_ERDOS_PROOF_NODE_IDS = new Set(
  Array.from({ length: 157 }, (_, index) => index + 1),
);

export function isOriginalErdosProofNode(nodeId: number): boolean {
  return ORIGINAL_ERDOS_PROOF_NODE_IDS.has(nodeId);
}

export type ErdosNodeObligationStatus = "proved" | "partial" | "missing";

export interface ErdosNodeObligation {
  /** Stable across rewording so a demotion cannot silently erase the task. */
  obligationId: string;
  title: string;
  statement: string;
  status: ErdosNodeObligationStatus;
  /** Lean-owned proof steps supplying evidence; empty for an unproved property. */
  evidenceStepIds: readonly string[];
}

export interface ErdosNodeObligationProgress {
  proved: number;
  total: number;
  remaining: number;
}

// Exact gaps between the current Lean endpoint and the claim printed in
// original_erdos_64_proof.tex. These are deliberately kept separately from
// generated Lean evidence: demoting a node preserves every outstanding task,
// while implementing a task requires a proof-step declaration group. The
// public ledger below merges both sides into stable, status-bearing records.
const ORIGINAL_ERDOS_NODE_PAPER_GAPS: Readonly<Record<number, readonly string[]>> = {
  24: [
    "Prove the original θ ≤ θwin + o(1) conclusion and its high-entropy numerical bound 0.01198542083… on the same node-[21] context.",
  ],
  48: [
    "Upgrade the repaired finite realized/open split to the original global forced-curvature inequality cΩW₂(R) ≥ Kwin|R| − o(|R|), with the printed high-entropy constant.",
  ],
  49: [
    "Identify the supplied finite state family with the manuscript family 𝒢(R), so the implemented cardinality bookkeeping proves the original per-vertex remainder entropy.",
  ],
  50: [
    "Connect the exact finite power comparison to the original η(R) ≥ (log₂ n)/10 decision on the manuscript state family and preserve both branch semantics.",
  ],
  51: [
    "Complete the original high-entropy remainder branch beyond the verified logarithmic arithmetic handoff.",
  ],
  52: [
    "Construct the missing same-context joint window–remainder realization and authored demand bound, then derive the original bound on θ.",
  ],
  53: [
    "Supply the independent same-context quarter-budget semantics needed to turn the verified strict-low powered inequality into the original remaining-budget decision and its outgoing branch.",
  ],
  54: [
    "Derive the original entropy-cap contradiction from the completed high-entropy or insufficient-remaining-budget predecessor, with the predecessor branch provenance preserved.",
  ],
  55: [
    "Construct Residual C on exactly the no-branch of node [53], retaining the large remaining budget and every full-rank remainder invariant required downstream.",
  ],
  56: [
    "Prove the original net-deficiency cap below 1/4 for Residual C and transport that exact bound to the Part-V input.",
  ],
  70: [
    "Assemble the verified degree caps and local certificates into the single original fan-safe graph and P₁₃ certificate-graph output on the exact predecessor branch.",
  ],
  71: [
    "Implement the original exhaustive certificate-labelling presence decision and route both outcomes with their exact graph provenance.",
  ],
  72: [
    "Compose the verified local fan entries into the complete global fan-window ledger and decide B2 disjointness across different fan centres.",
  ],
  73: [
    "Turn B2 failure into the original minimal Type-B overlap obstruction, including the required induced connectivity, global window-stub count, and routed handoff data.",
  ],
  74: [
    "From the B2-holds branch, prove the original bridge reduction N₀(X) ≥ 0 outside route 8 rather than only the current local state-space stratification.",
  ],
  84: [
    "Construct the canonical ordinary/grouped support family, prove both coefficient-208 incidence bounds, and derive the original global factor-416 fan-mass estimate.",
  ],
  129: [
    "Construct the nonempty full active baseline coordinate family and prove the original linear bound Espine ≤ CE n from predecessor data.",
  ],
  131: [
    "Derive the original free-pair entropy sandwich |Πfree| ≤ Espine + (σ/2 + 1) log₂ n; the implemented free-anchor/blocker routing is only its local input.",
  ],
  144: [
    "Route every classified bottleneck leaf to one of the original outputs: a named sparse exit, a fully decorated Type-B handoff, or the near-cubic spine.",
    "Provide the missing attachment/response connectors without assuming the sparse exit, CT3 equivalence, or Type-B payload that this node must construct.",
  ],
  153: [
    "Construct the graph-owned F2–F5 semantics on the exact stage-major cold schedule, including compatible-context response and route-8 data.",
    "Complete the G1/G2/G3 bounded-germ consumers and prove the original first-failure lower bound Ngerm ≥ 13C/Dcold − o(n).",
  ],
};

const DEMOTED_PREDECESSOR_GAPS: Readonly<Record<number, readonly string[]>> =
  Object.fromEntries([
    ...Array.from({ length: 21 }, (_, index) => {
      const nodeId = index + 27;
      const statement = nodeId >= 31
        ? "Restore exact provenance from nodes [24]–[26], including the simultaneous-rank producer, and construct the graph-specific omitted-response-vector handoff to the existing rank-drop exit before this node can be green."
        : "Restore this node's exact predecessor provenance from the completed nodes [24]–[26], including the simultaneous-rank producer required by the original flow."
      return [nodeId, [statement]] as const;
    }),
    [65, [
      "Construct every outgoing payload field prescribed at node [65]: the assigned carrier, its retained reserve, and the per-centre certificate data consumed by the original edges to nodes [70]–[72].",
    ]] as const,
    ...[...Array.from({ length: 9 }, (_, index) => index + 67),
      ...Array.from({ length: 7 }, (_, index) => index + 78)].map((nodeId) => [
      nodeId,
      ["Restore exact provenance through the original [64] → [65] handoff by supplying its assigned carrier, reserve, and per-centre certificate producer before consuming this node."],
    ] as const),
    ...Array.from({ length: 4 }, (_, index) => {
      const nodeId = index + 125;
      return [nodeId, [
        nodeId === 125
          ? "Construct the original sparse-pressure survivor by proving absence of all five named sparse-exit families on the actual selected demands, pairs, and baseline coordinates."
          : "Restore exact predecessor provenance through node [125] by producing the original sparse-pressure survivor after all five named sparse exits have been excluded.",
      ]] as const;
    }),
    ...Array.from({ length: 14 }, (_, index) => {
      const nodeId = index + 130;
      return [nodeId, [
        nodeId === 131
          ? "Restore the original node-[129] nonempty active-baseline proof Espine = O(n), then prove the node-[131] free-pair entropy bound before using this downstream result."
          : "Restore exact predecessor provenance by proving the original node-[129] nonempty active baseline and Espine = O(n) estimate before using this downstream result.",
      ]] as const;
    }),
    [155, [
      "Restore exact provenance from the completed nodes [153]–[154] by constructing the full graph-owned germ producer before invoking this closing node.",
    ]] as const,
    [151, [
      "Construct and consume the exact node-[150] surviving-cold output; the existing local theorem reconstructs the cold list from nodes [21]/[145] and therefore does not yet prove the original [150] → [151] handoff.",
    ]] as const,
    [152, [
      "Restore exact predecessor provenance from a completed node [151] before applying the already verified 15-stub and 13-branch-excess arithmetic.",
    ]] as const,
  ]);

const ORIGINAL_ERDOS_NODE_REMAINING: Readonly<Record<number, readonly string[]>> =
  Object.fromEntries(
    [...new Set([
      ...Object.keys(ORIGINAL_ERDOS_NODE_PAPER_GAPS).map(Number),
      ...Object.keys(DEMOTED_PREDECESSOR_GAPS).map(Number),
    ])].map((nodeId) => [
      nodeId,
      [
        ...(ORIGINAL_ERDOS_NODE_PAPER_GAPS[nodeId] ?? []),
        ...(DEMOTED_PREDECESSOR_GAPS[nodeId] ?? []),
      ],
    ]),
  );

export const ORIGINAL_ERDOS_NODE_OBLIGATIONS: Readonly<
  Record<number, readonly ErdosNodeObligation[]>
> = Object.fromEntries(
  Object.entries(ORIGINAL_ERDOS_NODE_REMAINING).map(([nodeId, obligations]) => [
    Number(nodeId),
    obligations.map((statement, index) => ({
      obligationId: `node-${nodeId}-remaining-${index + 1}`,
      title: `Original-paper obligation ${index + 1}`,
      statement,
      status: "missing" as const,
      evidenceStepIds: [],
    })),
  ]),
);

function auditedObligation(
  obligationId: string,
  statement: string,
  status: ErdosNodeObligationStatus,
  evidenceStepIds: readonly string[] = [],
): ErdosNodeObligation {
  return { obligationId, title: obligationId, statement, status, evidenceStepIds };
}

const SURPLUS_SCALE_EVIDENCE = ["erdos.surplus-scale-split"] as const;
const SPARSE_ENVELOPE_EVIDENCE = ["erdos.sparse-envelope"] as const;
const SURPLUS_CT6_EVIDENCE = ["erdos.surplus-ct6"] as const;
const BASELINE_EVIDENCE = ["erdos.baseline-spine-demand"] as const;
const WEIGHTED_COLD_EVIDENCE = ["erdos.p13-weighted-live-cold"] as const;
const STRUCTURAL_FRONTIER_EVIDENCE = ["erdos.p13-same-window-structural-frontier"] as const;
const ATTACHMENT_EVIDENCE = ["erdos.p13-actual-attachment-cold-fork"] as const;
const LONG_RESPONSE_EVIDENCE = ["erdos.p13-long-prefix-response-producer"] as const;
const D4_RESPONSE_EVIDENCE = ["erdos.p13-component-d4d7-semantic-consumer"] as const;
const DYADIC_TERMINAL_EVIDENCE = ["erdos.p13-same-window-dyadic-terminal"] as const;
const DENSITY_HANDOFF_EVIDENCE = ["erdos.p13-density-handoff"] as const;
const P13_PACKING_EVIDENCE = ["erdos.p13-packing"] as const;
const NODE146_THRESHOLD_EVIDENCE = ["erdos.p13-node146-route8-threshold"] as const;
const NODE147_ARITHMETIC_EVIDENCE = ["erdos.p13-node147-private-carrier-arithmetic"] as const;
const NODE148_HOT_DECISION_EVIDENCE = ["erdos.p13-node148-live-hot-decision"] as const;
const NODE149_DENSITY_EVIDENCE = ["erdos.p13-node149-density-cap"] as const;
const NODE150_COLD_MASS_EVIDENCE = ["erdos.p13-node150-cold-mass"] as const;
const NODE154_CLASSIFIER_EVIDENCE = ["erdos.p13-node154-local-classifier"] as const;
const TYPE_A_57_63_EVIDENCE = ["erdos.type-a-nodes57-63-local-provenance"] as const;
const TYPE_A_86_88_EVIDENCE = ["erdos.type-a-nodes86-88-local-thresholds"] as const;
const TYPE_A_89_EVIDENCE = ["erdos.type-a-node89-local-saturation"] as const;
const NODE153_PRODUCED_SUPPORT_EVIDENCE = ["erdos.p13-node153-produced-support-coverage"] as const;
const NODE153_EXACT_CONTINUATION_EVIDENCE = ["erdos.p13-node153-exact-continuation"] as const;
const NODE153_COMPONENT_CORRIDOR_EVIDENCE = ["erdos.p13-node153-restricted-component-corridor"] as const;

/** Property-level ledgers audited directly against the two root ledger files. */
export const AUDITED_ERDOS_NODE_OBLIGATIONS: Readonly<
  Record<number, readonly ErdosNodeObligation[]>
> = {
  23: [
    auditedObligation("N23-PROV", "Consume the exact node-[22] yes-edge payload on the identical node-[21] packing and package context.", "proved", DENSITY_HANDOFF_EVIDENCE),
    auditedObligation("N23-OVERFLOW", "Prove the strict reverse of the corrected finite window cap, retaining the explicit scale-loss and skeleton-normalization errors.", "proved", DENSITY_HANDOFF_EVIDENCE),
    auditedObligation("N23-WORK", "Use one exact natural-number comparison on the already selected packing; do not scan graph, context, Boolean-state, or universe families.", "proved", DENSITY_HANDOFF_EVIDENCE),
  ],
  24: [
    auditedObligation("N24-PROV", "Retain the exact node-[22] no-edge and identical node-[21] packing.", "proved", DENSITY_HANDOFF_EVIDENCE),
    auditedObligation("N24-FINITE-CAP", "Prove the corrected finite window cap with scale-loss and powered-skeleton normalization error explicit.", "proved", DENSITY_HANDOFF_EVIDENCE),
    auditedObligation("N24-HOT-COLD", "Retain the exact sequential hot/cold payment on the identical packing.", "proved", DENSITY_HANDOFF_EVIDENCE),
    auditedObligation("N24-SCALE-LOSS", "Prove the discarded-scale loss is at most thirty per accepted hot owner.", "proved", DENSITY_HANDOFF_EVIDENCE),
    auditedObligation("N24-ERROR-LITTLE-O", "Assemble the complete normalization correction and prove it is o(n log n), yielding theta <= theta_win + o(1).", "proved", DENSITY_HANDOFF_EVIDENCE),
    auditedObligation("N24-HIGH-ENTROPY-HANDOFF", "Emit the exact normalized high-entropy proposition as a typed downstream obligation on the identical packing; node [52], not node [24], must later prove it from joint window–remainder accounting.", "proved", DENSITY_HANDOFF_EVIDENCE),
    auditedObligation("N24-REMAINDER-FINITE", "Derive the exact error-bearing large-remainder connector.", "proved", DENSITY_HANDOFF_EVIDENCE),
    auditedObligation("N24-REMAINDER-ASYMPTOTIC", "Normalize the remainder connector to |R| >= (1-13 theta_win)n-o(n).", "proved", DENSITY_HANDOFF_EVIDENCE),
    auditedObligation("N24-TAU-CONSTANT", "Prove the exact rational value tau_win is below one quarter.", "proved", DENSITY_HANDOFF_EVIDENCE),
    auditedObligation("N24-TAU-TRANSPORT", "Transport the actual packing bound to tau(theta) <= tau_win + o(1).", "proved", DENSITY_HANDOFF_EVIDENCE),
    auditedObligation("N24-WORK", "Use constant local arithmetic work and only the declared hot, remainder, and cold schedules downstream.", "proved", DENSITY_HANDOFF_EVIDENCE),
  ],
  25: [
    auditedObligation("N25-PROV", "Consume the literal corrected node-[24] payload on the identical node-[21] packing.", "proved", P13_PACKING_EVIDENCE),
    auditedObligation("N25-PARTITION", "Retain the exact CT12 packing/remainder partition and finite remainder floor.", "proved", P13_PACKING_EVIDENCE),
    auditedObligation("N25-FREE", "Retain remainder and componentwise induced-P13 freeness.", "proved", P13_PACKING_EVIDENCE),
    auditedObligation("N25-LARGE", "Derive the numerical large-remainder estimate from node [24] on the same graph.", "proved", P13_PACKING_EVIDENCE),
    auditedObligation("N25-WORK", "Perform no new graph scan; reuse the selected packing and zero-check connector.", "proved", P13_PACKING_EVIDENCE),
  ],
  26: [
    auditedObligation("N26-HANDOFF", "Carry exactly node [25]'s residual across the Part-I/Part-II panel boundary without adding a new graph, packing, remainder, hypothesis, or case split.", "proved", P13_PACKING_EVIDENCE),
  ],
  27: [
    auditedObligation("N27-PROV", "Consume the exact node-[26] residual on the identical graph, packing, and remainder.", "proved", P13_PACKING_EVIDENCE),
    auditedObligation("N27-INDUCED-CORE", "Prove that the exact remainder has no induced internal support of minimum degree at least three.", "proved", P13_PACKING_EVIDENCE),
    auditedObligation("N27-SUBGRAPH-CORE", "Prove the manuscript's stronger formulation: no finite internal subgraph of the exact remainder has minimum degree at least three.", "proved", P13_PACKING_EVIDENCE),
    auditedObligation("N27-WORK", "Reuse the node-[26] proof fields with zero new graph, component, subgraph, or support scans.", "proved", P13_PACKING_EVIDENCE),
  ],
  28: [
    auditedObligation("N28-PROV", "Consume the exact node-[27] output on the identical graph, packing, and remainder.", "proved", ["erdos.p13-positive-deficiency"]),
    auditedObligation("N28-DEGREE", "Define d_R(v) as the induced degree of v in the literal remainder.", "proved", ["erdos.p13-positive-deficiency"]),
    auditedObligation("N28-FORMULA", "Define def+(R) as the sum over v in R of max(0,3-d_R(v)), represented by natural subtraction.", "proved", ["erdos.p13-positive-deficiency"]),
    auditedObligation("N28-CORE", "Retain node [27]'s no-internal-three-core property unchanged.", "proved", ["erdos.p13-positive-deficiency"]),
    auditedObligation("N28-WORK", "Use one induced-neighbour scan per remainder vertex, at most n^2 checks, without enumerating supports or subgraphs.", "proved", ["erdos.p13-positive-deficiency"]),
  ],
  29: [
    auditedObligation("N29-PROV", "Consume the exact dependent node-[28] output on the identical graph, packing, and remainder.", "proved", ["erdos.p13-external-incidence-supply"]),
    auditedObligation("N29-BOUNDARY", "Charge every positive-deficiency unit to a literal incidence leaving the remainder, proving def+(R) <= e(R,W).", "proved", ["erdos.p13-external-incidence-supply"]),
    auditedObligation("N29-TOKENS", "Embed every R-W incidence in the selected-window external-token schedule.", "proved", ["erdos.p13-external-incidence-supply"]),
    auditedObligation("N29-EXACT", "Prove the exact selected-window identity tokenCount = 15 p13 + sigma_W.", "proved", ["erdos.p13-external-incidence-supply"]),
    auditedObligation("N29-SUPPLY", "Derive def+(R) <= 15 p13 + sigma_W and the surplus-adjusted inequality after subtracting sigma_R.", "proved", ["erdos.p13-external-incidence-supply"]),
    auditedObligation("N29-SPINE", "Retain the bounded-surplus square certificate that supplies the manuscript's o(n) near-cubic error.", "proved", ["erdos.p13-external-incidence-supply"]),
    auditedObligation("N29-WORK", "Use at most 13 n^2 local incidence checks on the selected windows, without enumerating paths, packings, supports, subgraphs, graphs, states, or contexts.", "proved", ["erdos.p13-external-incidence-supply"]),
  ],
  30: [
    auditedObligation("N30-PROV", "Consume the exact dependent node-[29] output on the identical graph, packing, and remainder.", "proved", ["erdos.p13-wedge-lower"]),
    auditedObligation("N30-COMPONENT", "For every remainder component C, prove W2(C) >= 3|V(C)| - 2 def+(C) by the local degree count.", "proved", ["erdos.p13-wedge-lower"]),
    auditedObligation("N30-AGGREGATE", "Apply the same exact degree-count theorem to the literal remainder and obtain W2(R) >= 3|R| - 2 def+(R).", "proved", ["erdos.p13-wedge-lower"]),
    auditedObligation("N30-WINDOW", "Combine node [29]'s finite deficiency supply with the aggregate wedge floor, retaining the selected-window and total-surplus error exactly.", "proved", ["erdos.p13-wedge-lower"]),
    auditedObligation("N30-WINDOW-RATE", "Transport the window-only deficiency coefficient to omega_win = 3 - 2 tau_win and verify the manuscript's printed decimal lower approximation.", "proved", ["erdos.p13-wedge-lower"]),
    auditedObligation("N30-HIGH-RATE", "Conditionally transport the separately supplied high-entropy deficiency rate 0.21296321056... to omega = 2.57407357888..., without assuming that branch at node [30].", "proved", ["erdos.p13-wedge-lower"]),
    auditedObligation("N30-SPINE", "Retain the exact near-cubic bounded-error certificate inherited from node [29].", "proved", ["erdos.p13-wedge-lower"]),
    auditedObligation("N30-WORK", "Use at most n^2 local induced-neighbour checks and arithmetic transport only, with no component, support, path, quotient, context, subgraph, graph, or state-universe enumeration.", "proved", ["erdos.p13-wedge-lower"]),
  ],
  31: [
    auditedObligation("N31-PROV", "Consume the exact dependent node-[30] output on the identical graph, packing, remainder, and wedge profile.", "proved", ["erdos.p13-curvature-target-rank"]),
    auditedObligation("N31-COORDINATES", "Define the raw curvature tests as exactly one remainder center and one canonical unordered pair of distinct internal neighbours.", "proved", ["erdos.p13-curvature-target-rank"]),
    auditedObligation("N31-COUNT", "Prove that the declared coordinate schedule has cardinality exactly W2(R), and at most n^3.", "proved", ["erdos.p13-curvature-target-rank"]),
    auditedObligation("N31-RESPONSE", "Evaluate each coordinate by the exact target response of its literal three-vertex supported piece under every outside context.", "proved", ["erdos.p13-curvature-target-rank"]),
    auditedObligation("N31-SURVIVAL", "Define survival of a subfamily as label-injectivity under every functional admissible quotient of the exact response profile.", "proved", ["erdos.p13-curvature-target-rank"]),
    auditedObligation("N31-RANK", "Define rOmega(R) as the maximum cardinality of a surviving declared subfamily and prove the maximum is attained.", "proved", ["erdos.p13-curvature-target-rank"]),
    auditedObligation("N31-UPPER", "Prove rOmega(R) <= W2(R).", "proved", ["erdos.p13-curvature-target-rank"]),
    auditedObligation("N31-WORK", "Use only the literal wedge schedule; define the maximum propositionally without evaluating a powerset, quotient family, context family, support family, path family, subgraph family, or graph universe.", "proved", ["erdos.p13-curvature-target-rank"]),
  ],
  32: [
    auditedObligation("N32-PROV", "Consume the exact dependent node-[31] output on the identical graph, remainder, wedge family, response profile, and target-rank object.", "proved", ["erdos.p13-curvature-rank-decision"]),
    auditedObligation("N32-UPPER", "Use node [31]'s bound rOmega(R) <= W2(R) on the literal raw-coordinate schedule.", "proved", ["erdos.p13-curvature-rank-decision"]),
    auditedObligation("N32-YES", "Represent the original yes edge by the proof-carrying strict rank-loss payload rOmega(R) < W2(R).", "proved", ["erdos.p13-curvature-rank-decision"]),
    auditedObligation("N32-NO", "Represent the original no edge by the proof-carrying exact full-rank payload rOmega(R) = W2(R).", "proved", ["erdos.p13-curvature-rank-decision"]),
    auditedObligation("N32-EXHAUSTIVE", "Prove that the strict-loss and exact-full constructors are mutually exhaustive, with no third case or new diagram edge.", "proved", ["erdos.p13-curvature-rank-decision"]),
    auditedObligation("N32-WORK", "Perform zero executable scans after node [31], without evaluating coordinate subfamilies, quotients, contexts, supports, paths, subgraphs, graphs, or state universes.", "proved", ["erdos.p13-curvature-rank-decision"]),
  ],
  33: [
    auditedObligation("N33-PROV", "Consume the exact node-[32] output together with its literal strict-rank-loss yes-edge proof on the identical target-rank object.", "proved", ["erdos.p13-curvature-dependence-open"]),
    auditedObligation("N33-NONSURVIVAL", "Derive that the complete declared raw-wedge family does not survive every functional admissible quotient.", "proved", ["erdos.p13-curvature-dependence-open"]),
    auditedObligation("N33-QUOTIENT", "Extract one admitted quotient that is non-injective on the declared raw coordinates.", "proved", ["erdos.p13-curvature-dependence-open"]),
    auditedObligation("N33-PAIR", "Retain two distinct declared raw curvature coordinates with the same quotient value.", "proved", ["erdos.p13-curvature-dependence-open"]),
    auditedObligation("N33-FUNCTIONAL", "Package the identification as a finite functional dependence with one determined coordinate and a singleton declared basis not containing it.", "proved", ["erdos.p13-curvature-dependence-open"]),
    auditedObligation("N33-HANDOFF", "Retain the quotient and pair circuit unchanged for the existing cross-panel Branch-D node [35].", "proved", ["erdos.p13-curvature-dependence-open"]),
    auditedObligation("N33-WORK", "Proof-select the circuit with zero executable searches and no coordinate powerset, quotient family, context family, support family, path family, subgraph family, graph universe, or state universe.", "proved", ["erdos.p13-curvature-dependence-open"]),
  ],
  34: [
    auditedObligation("N34-PROV", "Consume the exact node-[32] output together with its literal full-rank no-edge equality on the identical target-rank object.", "proved", ["erdos.p13-full-curvature-rank"]),
    auditedObligation("N34-EQUALITY", "Retain the exact finite equality rOmega(R) = W2(R).", "proved", ["erdos.p13-full-curvature-rank"]),
    auditedObligation("N34-NODROP", "Prove that no strict target-rank loss remains on this edge.", "proved", ["erdos.p13-full-curvature-rank"]),
    auditedObligation("N34-LOWER", "Derive the full-rank lower bound W2(R) <= rOmega(R), which is stronger than the displayed near-full asymptotic residual.", "proved", ["erdos.p13-full-curvature-rank"]),
    auditedObligation("N34-FAMILY", "Retain an actual declared subfamily surviving every functional admissible quotient whose cardinality is exactly W2(R).", "proved", ["erdos.p13-full-curvature-rank"]),
    auditedObligation("N34-WORK", "Perform zero new executable scans and evaluate no coordinate powerset, quotient family, context family, support family, path family, subgraph family, graph universe, or state universe.", "proved", ["erdos.p13-full-curvature-rank"]),
  ],
  35: [
    auditedObligation("N35-PROV", "Consume exactly the node-[33] Branch-D residual on the identical graph, remainder, response profile, and strict-rank-loss edge.", "proved", ["erdos.remainder-curvature-rank"]),
    auditedObligation("N35-QUOTIENT", "Retain the same admitted functional quotient without rebuilding or re-auditing it.", "proved", ["erdos.remainder-curvature-rank"]),
    auditedObligation("N35-PAIR", "Retain the same two distinct declared raw curvature coordinates and their quotient-identification equation.", "proved", ["erdos.remainder-curvature-rank"]),
    auditedObligation("N35-BASIS", "Retain the singleton declared determining basis and the proof that the determined coordinate is not in it.", "proved", ["erdos.remainder-curvature-rank"]),
    auditedObligation("N35-IDENTITY", "Prove that the Part-II to Part-III connector is definitionally identity on the complete Branch-D carrier.", "proved", ["erdos.remainder-curvature-rank"]),
    auditedObligation("N35-WORK", "Perform zero new scans and enumerate no coordinate, quotient, context, support, path, subgraph, graph, or state family.", "proved", ["erdos.remainder-curvature-rank"]),
  ],
  36: [
    auditedObligation("N36-PROV", "Consume the exact green node-[35] Branch-D payload on the identical graph, remainder, admitted quotient, and pair circuit.", "proved", ["erdos.p13-curvature-context-validity"]),
    auditedObligation("N36-DECISION", "Represent exactly the original two edges: one concrete outside-context mismatch or equality in every declared outside context.", "proved", ["erdos.p13-curvature-context-validity"]),
    auditedObligation("N36-UNIVERSAL", "Project universal target-response equality for the identified raw wedges from the quotient's audited admissibility field.", "proved", ["erdos.p13-curvature-context-validity"]),
    auditedObligation("N36-NODEFECT", "Prove that no concrete distinguishing outside context exists for this admitted quotient.", "proved", ["erdos.p13-curvature-context-validity"]),
    auditedObligation("N36-EDGE", "Retain the universal constructor as the exact outgoing payload consumed by node [38], without introducing another case.", "proved", ["erdos.p13-curvature-context-validity"]),
    auditedObligation("N36-WORK", "Perform zero executable context checks and enumerate no context, coordinate, quotient, support, path, subgraph, graph, or state family.", "proved", ["erdos.p13-curvature-context-validity"]),
  ],
  37: [
    auditedObligation("N37-PROV", "Consume the exact green node-[36] output together with its literal no-edge concrete mismatch witness.", "proved", ["erdos.p13-curvature-target-defect-terminal"]),
    auditedObligation("N37-CONTEXT", "Retain the supplied outside context itself rather than searching or reconstructing a context family.", "proved", ["erdos.p13-curvature-target-defect-terminal"]),
    auditedObligation("N37-MISMATCH", "Retain the exact inequality between the two identified raw-wedge target responses in that context.", "proved", ["erdos.p13-curvature-target-defect-terminal"]),
    auditedObligation("N37-DEFECT", "Expose the concrete mismatch as precisely the target-defective quotient residual prescribed by the manuscript.", "proved", ["erdos.p13-curvature-target-defect-terminal"]),
    auditedObligation("N37-CLOSE", "Close only this no edge by contradiction with the admitted quotient's universal-response equality.", "proved", ["erdos.p13-curvature-target-defect-terminal"]),
    auditedObligation("N37-WORK", "Perform zero new checks and enumerate no context, coordinate, quotient, support, path, subgraph, graph, or state family.", "proved", ["erdos.p13-curvature-target-defect-terminal"]),
  ],
  38: [
    auditedObligation("N38-PROV", "Consume the exact green node-[36] universal-response edge on the identical admitted quotient and pair circuit.", "proved", ["erdos.p13-curvature-proper-representative-decision"]),
    auditedObligation("N38-NONINJECTIVE", "Prove that identifying the two retained distinct raw wedges makes the quotient proposal non-injective.", "proved", ["erdos.p13-curvature-proper-representative-decision"]),
    auditedObligation("N38-DECISION", "Represent exactly availability or absence of the certified smaller representative, with no additional diagram case.", "proved", ["erdos.p13-curvature-proper-representative-decision"]),
    auditedObligation("N38-REPRESENTATIVE", "Project the strictly smaller representative already certified by quotient admissibility.", "proved", ["erdos.p13-curvature-proper-representative-decision"]),
    auditedObligation("N38-BASELINE", "Retain strict rank decrease, the baseline proof, and target transport back to the selected graph.", "proved", ["erdos.p13-curvature-proper-representative-decision"]),
    auditedObligation("N38-YES", "Route the available representative through the original yes edge to node [39].", "proved", ["erdos.p13-curvature-proper-representative-decision"]),
    auditedObligation("N38-WORK", "Perform zero checks and enumerate no representative candidates, coordinates, quotients, contexts, supports, paths, subgraphs, graphs, or states.", "proved", ["erdos.p13-curvature-proper-representative-decision"]),
  ],
  39: [
    auditedObligation("N39-PROV", "Consume the exact green node-[38] yes-edge payload and its identical certified smaller representative.", "proved", ["erdos.p13-curvature-proper-compression-terminal"]),
    auditedObligation("N39-WITNESS", "Use the representative's inherited strict decrease, baseline proof, and target transport to construct a smaller target-avoiding baseline object.", "proved", ["erdos.p13-curvature-proper-compression-terminal"]),
    auditedObligation("N39-CLOSE", "Contradict the selected graph's minimal-counterexample context, closing exactly the proper-compression terminal.", "proved", ["erdos.p13-curvature-proper-compression-terminal"]),
    auditedObligation("N39-SCOPE", "Leave node [38]'s no edge toward enlarged connected support untouched for node [40].", "proved", ["erdos.p13-curvature-proper-compression-terminal"]),
    auditedObligation("N39-WORK", "Perform zero new checks and enumerate no representative, coordinate, quotient, context, support, path, subgraph, graph, or state family.", "proved", ["erdos.p13-curvature-proper-compression-terminal"]),
  ],
  57: [
    auditedObligation("V-57-01", "Consume the exact node-[56] strict-quarter handoff on the identical remainder.", "partial", TYPE_A_57_63_EVIDENCE),
    auditedObligation("V-57-02", "Retain that predecessor definitionally, without changing support or decomposition.", "proved", TYPE_A_57_63_EVIDENCE),
  ],
  58: [
    auditedObligation("V-58-01", "Consume the exact node-[57] residual.", "partial", TYPE_A_57_63_EVIDENCE),
    auditedObligation("V-58-02", "Retain the identical remainder.", "proved", TYPE_A_57_63_EVIDENCE),
    auditedObligation("V-58-03", "Define the exact quarter-unit net-charge numerator 4 def+(R)-|R|.", "proved", TYPE_A_57_63_EVIDENCE),
  ],
  59: [
    auditedObligation("V-59-01", "Consume the exact node-[58] residual reached from node [56].", "partial", TYPE_A_57_63_EVIDENCE),
    auditedObligation("V-59-02", "Prove the nonnegative yes branch is impossible under the retained strict-quarter inequality.", "proved", TYPE_A_57_63_EVIDENCE),
    auditedObligation("V-59-03", "Route the original no edge with strict negative net charge on the same remainder.", "proved", TYPE_A_57_63_EVIDENCE),
  ],
  60: [
    auditedObligation("V-60-01", "Close the nonnegative terminal by contradiction with node [59]'s strict negative charge.", "partial", TYPE_A_57_63_EVIDENCE),
  ],
  61: [
    auditedObligation("V-61-01", "Consume the exact node-[59] negative residual on the same remainder.", "partial", TYPE_A_57_63_EVIDENCE),
    auditedObligation("V-61-02", "Construct the canonical remainder-component list.", "proved", TYPE_A_57_63_EVIDENCE),
    auditedObligation("V-61-03", "Express the total quarter charge as the sum of component charges.", "proved", TYPE_A_57_63_EVIDENCE),
    auditedObligation("V-61-04", "Execute CT11 and select an actually negative component.", "proved", TYPE_A_57_63_EVIDENCE),
    auditedObligation("V-61-05", "Retain exact inclusion in the original remainder.", "proved", TYPE_A_57_63_EVIDENCE),
  ],
  62: [
    auditedObligation("V-62-01", "Consume the exact node-[61] localized support.", "partial", TYPE_A_57_63_EVIDENCE),
    auditedObligation("V-62-02", "Test whether the support contains a degree-at-least-four vertex.", "proved", TYPE_A_57_63_EVIDENCE),
    auditedObligation("V-62-03", "Route yes to the existing node [64] Type-B handoff.", "proved", TYPE_A_57_63_EVIDENCE),
    auditedObligation("V-62-04", "Route no to the existing node [63] Type-A handoff.", "proved", TYPE_A_57_63_EVIDENCE),
  ],
  63: [
    auditedObligation("V-63-01", "Consume the exact no-high-center output of node [62].", "partial", TYPE_A_57_63_EVIDENCE),
    auditedObligation("V-63-02", "Retain a connected Type-A support.", "proved", TYPE_A_57_63_EVIDENCE),
    auditedObligation("V-63-03", "Prove every ambient vertex in the support is cubic.", "proved", TYPE_A_57_63_EVIDENCE),
    auditedObligation("V-63-04", "Prove the induced support is subcubic.", "proved", TYPE_A_57_63_EVIDENCE),
    auditedObligation("V-63-05", "Prove the induced support has empty internal 3-core.", "proved", TYPE_A_57_63_EVIDENCE),
  ],
  86: [
    auditedObligation("VIII-86-01", "Consume the exact no-high Type-A support from node [63].", "partial", TYPE_A_86_88_EVIDENCE),
    auditedObligation("VIII-86-02", "Retain the localized strict negative net charge.", "proved", TYPE_A_86_88_EVIDENCE),
    auditedObligation("VIII-86-03", "Prove sigma(X)=0 on the identical support.", "proved", TYPE_A_86_88_EVIDENCE),
    auditedObligation("VIII-86-04", "Derive 4 def+(X)<|X|.", "proved", TYPE_A_86_88_EVIDENCE),
    auditedObligation("VIII-86-05", "Perform no new graph-family search.", "proved", TYPE_A_86_88_EVIDENCE),
  ],
  87: [
    auditedObligation("VIII-87-01", "Consume the exact node-[86] residual.", "partial", TYPE_A_86_88_EVIDENCE),
    auditedObligation("VIII-87-02", "Prove the identical induced support is P13-free.", "proved", TYPE_A_86_88_EVIDENCE),
    auditedObligation("VIII-87-03", "Prove every two support vertices have an internal simple path of length at most eleven.", "proved", TYPE_A_86_88_EVIDENCE),
    auditedObligation("VIII-87-04", "Apply the subcubic Moore count and prove |X|<=6142.", "proved", TYPE_A_86_88_EVIDENCE),
    auditedObligation("VIII-87-05", "Use one local BFS/layer schedule with a polynomial work bound.", "proved", TYPE_A_86_88_EVIDENCE),
  ],
  88: [
    auditedObligation("VIII-88-01", "Consume the complete exact node-[87] residual.", "partial", TYPE_A_86_88_EVIDENCE),
    auditedObligation("VIII-88-02", "Define q(w)=3-d_X(w) on the identical support.", "proved", TYPE_A_86_88_EVIDENCE),
    auditedObligation("VIII-88-03", "Define the first saturated load H(w)=4q(w).", "proved", TYPE_A_86_88_EVIDENCE),
    auditedObligation("VIII-88-04", "For d_X(w)=2-j prove H_j=4(j+1).", "proved", TYPE_A_86_88_EVIDENCE),
    auditedObligation("VIII-88-05", "Prove H0<=4, H1<=8, and H2<=12.", "proved", TYPE_A_86_88_EVIDENCE),
    auditedObligation("VIII-88-06", "Route only to the existing node [89] with constant arithmetic work.", "proved", TYPE_A_86_88_EVIDENCE),
  ],
  89: [
    auditedObligation("VIII-89-01", "Consume a typed immediate node-[88] residual on the identical Type-A support.", "partial", TYPE_A_89_EVIDENCE),
    auditedObligation("VIII-89-02", "Define q(w) and the canonical receiver load L(w).", "proved", TYPE_A_89_EVIDENCE),
    auditedObligation("VIII-89-03", "Decide whether some receiver has L(w)>=4q(w).", "proved", TYPE_A_89_EVIDENCE),
    auditedObligation("VIII-89-04", "On no, prove every receiver has L(w)<=4q(w)-1 and route to node [90].", "proved", TYPE_A_89_EVIDENCE),
    auditedObligation("VIII-89-05", "On yes, retain an actual saturated receiver and route to node [93].", "proved", TYPE_A_89_EVIDENCE),
    auditedObligation("VIII-89-06", "Preserve exact predecessor identity and prove both routes exhaustive.", "proved", TYPE_A_89_EVIDENCE),
    auditedObligation("VIII-89-07", "Inspect only actual support vertices and receiver fibres with polynomial work.", "proved", TYPE_A_89_EVIDENCE),
    auditedObligation("VIII-89-08", "Retain the raw H0/H1/H2 threshold audit from the immediate predecessor.", "proved", TYPE_A_89_EVIDENCE),
  ],
  125: [
    auditedObligation("N125-PROV", "Retain the literal node-[20] strict non-near-cubic scale residual and identical node-[18] selected graph/label algebra.", "proved", SURPLUS_SCALE_EVIDENCE),
    auditedObligation("N125-LABEL", "The selected graph has passed the finite P13 label algebra used by this branch.", "proved", SURPLUS_SCALE_EVIDENCE),
    auditedObligation("N125-EXITS-DEFINE", "Define the five named sparse-exit families on actual selected demands, selected pairs, and baseline coordinates.", "missing"),
    auditedObligation("N125-EXITS-RUN", "Execute the original sparse-exit tests locally and exhaustively, retaining either an existing exit edge or the survivor branch.", "missing"),
    auditedObligation("N125-SURVIVE", "On the Part-X edge, prove none of the named sparse exits occurs for any scheduled coordinate.", "missing"),
    auditedObligation("N125-WORK", "Bound the actual local exit schedule polynomially without graph/context enumeration.", "partial", SURPLUS_SCALE_EVIDENCE),
  ],
  126: [
    auditedObligation("N126-PROV", "Consume the exact node-[125] survivor on the same graph.", "partial", SPARSE_ENVELOPE_EVIDENCE),
    auditedObligation("N126-EDGE", "Prove m <= 2n - 2.", "proved", SPARSE_ENVELOPE_EVIDENCE),
    auditedObligation("N126-SLACK", "Define lambda = 2n - 3 - m and sigma = 2m - 3n, and prove sigma = n - 6 - 2lambda.", "proved", SPARSE_ENVELOPE_EVIDENCE),
    auditedObligation("N126-SECOND", "Prove the equivalent division-free edge/surplus identity.", "proved", SPARSE_ENVELOPE_EVIDENCE),
    auditedObligation("N126-RUN", "Execute the actual local CT12 peeling certificate with trace, validity, totality, iterations, and linear work bound.", "proved", SPARSE_ENVELOPE_EVIDENCE),
  ],
  127: [
    auditedObligation("N127-PROV", "Consume the exact node-[126] output while retaining nodes [125]/[20].", "partial", BASELINE_EVIDENCE),
    auditedObligation("N127-SELECT", "Define the actual excess selector: exactly d(h)-3 incident ports per high center.", "proved", SURPLUS_CT6_EVIDENCE),
    auditedObligation("N127-CARD", "Prove A = P_exc and |A| = sigma(G).", "proved", BASELINE_EVIDENCE),
    auditedObligation("N127-ENDPOINT", "For every selected (h,x), prove d(h) >= 4, d(x) = 3, and N(x) = {h,a_p,b_p} with distinct shoulders.", "proved", BASELINE_EVIDENCE),
    auditedObligation("N127-WORK", "Scan only the actual vertex/slot schedule with a polynomial bound.", "proved", SURPLUS_CT6_EVIDENCE),
  ],
  128: [
    auditedObligation("N128-PROV", "Consume the identical node-[127] selected slot family and same graph.", "partial", BASELINE_EVIDENCE),
    auditedObligation("N128-RETURN", "Canonically choose a simple x-h return R_p in G-hx, first edge through one shoulder.", "proved", BASELINE_EVIDENCE),
    auditedObligation("N128-OPEN", "In the open case, produce canonical Q_p in G-x with length 2^j-1, j >= 2, from suppression/minimality.", "proved", BASELINE_EVIDENCE),
    auditedObligation("N128-TRI", "In the triangular case, retain the triangle and canonical return.", "proved", BASELINE_EVIDENCE),
    auditedObligation("N128-CANON", "Prove all response data are canonical functions of the selected graph order and port, with no caller witness.", "proved", BASELINE_EVIDENCE),
    auditedObligation("N128-WORK", "Account only for actual selected slots/paths; never enumerate ambient graphs or contexts.", "proved", SURPLUS_CT6_EVIDENCE),
  ],
  145: [
    auditedObligation("XI-145-01", "Consume the near-cubic node-[21] packing and its exact selected-window order.", "proved", WEIGHTED_COLD_EVIDENCE),
    auditedObligation("XI-145-02", "Define one live hot extension as a complete window package commuting with every already retained package.", "proved", WEIGHTED_COLD_EVIDENCE),
    auditedObligation("XI-145-03", "Process every packed window in packing order, accepting a compatible extension or rejecting that exact extension at the unchanged aggregate.", "proved", WEIGHTED_COLD_EVIDENCE),
    auditedObligation("XI-145-04", "Define the hot and cold families as the exact disjoint/exhaustive ledger projection.", "proved", WEIGHTED_COLD_EVIDENCE),
    auditedObligation("XI-145-05", "Retain recoverable simultaneous choices and bound their product by the common skeleton code.", "proved", WEIGHTED_COLD_EVIDENCE),
    auditedObligation("XI-145-06", "Use one local extension decision per actual packed window, with no ambient graph/context enumeration.", "proved", WEIGHTED_COLD_EVIDENCE),
  ],
  146: [
    auditedObligation("XI-146-01", "Define theta, tau(theta)=15theta/(1-13theta), and the strict theta < 1/78 decision.", "proved", NODE146_THRESHOLD_EVIDENCE),
    auditedObligation("XI-146-02", "Prove tau(theta) < 3/13 iff theta < 1/78, preserving strictness and denominator positivity.", "proved", NODE146_THRESHOLD_EVIDENCE),
    auditedObligation("XI-146-03", "Route yes to node [147] and no with theta >= 1/78 to node [148].", "proved", NODE146_THRESHOLD_EVIDENCE),
  ],
  147: [
    auditedObligation("XI-147-01", "Consume the literal node-[146] yes edge on the identical node-[145] ledger.", "proved", NODE147_ARITHMETIC_EVIDENCE),
    auditedObligation("XI-147-02", "Retain tau(theta) < 3/13.", "proved", NODE147_ARITHMETIC_EVIDENCE),
    auditedObligation("XI-147-03", "Prove tau(theta) < 12(1/4-tau(theta)).", "proved", NODE147_ARITHMETIC_EVIDENCE),
    auditedObligation("XI-147-04", "Record the equivalent positive margin 3-13 tau(theta) > 0.", "proved", NODE147_ARITHMETIC_EVIDENCE),
    auditedObligation("XI-147-05", "Consume the existing Type-A route-8 collection with exact basin count and same-context remainder.", "missing"),
    auditedObligation("XI-147-06", "Select three private essential carriers per basin and prove cross-entry disjoint boundary injection.", "missing"),
    auditedObligation("XI-147-07", "Derive the private-carrier upper budget 3N <= def+(R) <= tau|R|+o(|R|).", "missing"),
    auditedObligation("XI-147-08", "Derive the route-8 burden lower budget 3N >= 12(1/4-tau)|R|-o(|R|).", "missing"),
    auditedObligation("XI-147-09", "Absorb both eventual errors using the positive margin and conclude contradiction.", "missing"),
  ],
  148: [
    auditedObligation("XI-148-01", "Consume the identical node-[146] no residual with theta >= 1/78 and retain the exact final hot aggregate.", "proved", NODE148_HOT_DECISION_EVIDENCE),
    auditedObligation("XI-148-02a", "Define total, hot, cold, and corrected skeleton demands on the exact packing-order ledger.", "proved", NODE148_HOT_DECISION_EVIDENCE),
    auditedObligation("XI-148-02b", "Prove the simultaneous recoverable hot product fits the corrected allowance.", "proved", NODE148_HOT_DECISION_EVIDENCE),
    auditedObligation("XI-148-02c", "Prove the exact hot/cold demand partition and total payment bound.", "proved", NODE148_HOT_DECISION_EVIDENCE),
    auditedObligation("XI-148-02d", "Decide the corrected total cap with one comparison.", "proved", NODE148_HOT_DECISION_EVIDENCE),
    auditedObligation("XI-148-03a", "Route yes to node [149] with the corrected finite density handoff.", "proved", NODE148_HOT_DECISION_EVIDENCE),
    auditedObligation("XI-148-03b", "Route no to node [150] with failed cap, hot payment, cold shortfall, and cold nonemptiness.", "proved", NODE148_HOT_DECISION_EVIDENCE),
    auditedObligation("XI-148-04", "Prove exhaustiveness and a constant local work certificate without ambient enumeration.", "proved", NODE148_HOT_DECISION_EVIDENCE),
  ],
  149: [
    auditedObligation("XI-149-01", "Consume the particular node-[148] yes payload and retain the complete dependent predecessor chain.", "proved", NODE149_DENSITY_EVIDENCE),
    auditedObligation("XI-149-02", "Retain the corrected finite density cap selected by node [148].", "proved", NODE149_DENSITY_EVIDENCE),
    auditedObligation("XI-149-03", "Export the exact cross-multiplied theta cap without dropping normalization error.", "proved", NODE149_DENSITY_EVIDENCE),
    auditedObligation("XI-149-04", "Verify theta_win's exact coefficient and decimal bracket and retain the corrected remainder consequence.", "proved", NODE149_DENSITY_EVIDENCE),
    auditedObligation("XI-149-05", "Bound the complete normalization error uniformly by o(n log n) and conclude theta <= theta_win + o(1).", "proved", NODE149_DENSITY_EVIDENCE),
    auditedObligation("XI-149-06", "Perform no new search and expose a polynomial local work bound.", "proved", NODE149_DENSITY_EVIDENCE),
  ],
  150: [
    auditedObligation("XI-150-01", "Consume the literal node-[148] no edge with the identical node-[146] no payload and node-[145] ledger.", "proved", NODE150_COLD_MASS_EVIDENCE),
    auditedObligation("XI-150-02", "Define C as the exact cold count of the sequential rejection ledger.", "proved", NODE150_COLD_MASS_EVIDENCE),
    auditedObligation("XI-150-03", "Retain failed hot comparison, hot payment/cold shortfall, and prove C > 0.", "proved", NODE150_COLD_MASS_EVIDENCE),
    auditedObligation("XI-150-04", "Prove the exact finite form of C >= (theta-theta_win)n with correction explicit.", "proved", NODE150_COLD_MASS_EVIDENCE),
    auditedObligation("XI-150-05", "Prove the correction becomes o(n) after division by the positive binary-log budget.", "proved", NODE150_COLD_MASS_EVIDENCE),
    auditedObligation("XI-150-06", "Evaluate the route-8 threshold coefficient exactly.", "proved", NODE150_COLD_MASS_EVIDENCE),
    auditedObligation("XI-150-07", "Evaluate the conditional negative-net threshold coefficient exactly.", "proved", NODE150_COLD_MASS_EVIDENCE),
    auditedObligation("XI-150-08", "Certify both printed decimal lower coefficients using the longer manuscript rate.", "proved", NODE150_COLD_MASS_EVIDENCE),
    auditedObligation("XI-150-09", "Retain every surviving-cold exclusion and the exact near-cubic spine payload for node [151].", "missing"),
  ],
  151: [
    auditedObligation("XI-151-01", "Consume the exact node-[150] cold family and surviving near-cubic branch state.", "missing"),
    auditedObligation("XI-151-02", "Partition that cold family into ambient-cubic and non-cubic windows.", "proved", WEIGHTED_COLD_EVIDENCE),
    auditedObligation("XI-151-03", "Charge each non-cubic cold window injectively to positive total surplus.", "proved", WEIGHTED_COLD_EVIDENCE),
    auditedObligation("XI-151-04", "Derive the exact finite square-root form of all-but-o(n) non-cubic loss.", "proved", WEIGHTED_COLD_EVIDENCE),
    auditedObligation("XI-151-05", "Export the retained ambient-cubic cold family to node [152].", "proved", WEIGHTED_COLD_EVIDENCE),
  ],
  152: [
    auditedObligation("XI-152-01", "Consume the exact ambient-cubic family produced at node [151].", "partial", WEIGHTED_COLD_EVIDENCE),
    auditedObligation("XI-152-02", "Prove one induced P13 has degree sum 39, internal contribution 24, and exactly 15 external stubs.", "proved", WEIGHTED_COLD_EVIDENCE),
    auditedObligation("XI-152-03", "Select the first two transit stubs and exactly the remaining 13 branch-excess stubs in canonical local order.", "proved", WEIGHTED_COLD_EVIDENCE),
    auditedObligation("XI-152-04", "Form the complete cold schedule without importing hot/unrelated windows or duplicating a cold endpoint.", "proved", WEIGHTED_COLD_EVIDENCE),
    auditedObligation("XI-152-05", "Prove b(S_cold) >= 13C-o(n) in exact finite form.", "proved", WEIGHTED_COLD_EVIDENCE),
  ],
  153: [
    auditedObligation("XI-153-01", "Consume each exact selected node-[152] branch-excess half-edge once.", "partial", WEIGHTED_COLD_EVIDENCE),
    auditedObligation("XI-153-02", "Construct its actual outside component, cyclic successor stub, and lexicographically first simple return corridor.", "proved", NODE153_COMPONENT_CORRIDOR_EVIDENCE),
    auditedObligation("XI-153-03", "Define the finite structural cut state, Q_cold, and bounds M_cold, B_cold, D_cold.", "partial", STRUCTURAL_FRONTIER_EVIDENCE),
    auditedObligation("XI-153-04", "At each stage test F1 first, then F2, F3, F4; enter F5 only when all earlier alternatives are negative.", "proved", NODE153_EXACT_CONTINUATION_EVIDENCE),
    auditedObligation("XI-153-05", "Route F1 to a literal power-of-two cycle.", "proved", STRUCTURAL_FRONTIER_EVIDENCE),
    auditedObligation("XI-153-06", "Route F2 to one literal distinguishing context/target-defective quotient.", "partial", NODE153_EXACT_CONTINUATION_EVIDENCE),
    auditedObligation("XI-153-07", "Route F3 universal response plus strict smaller representative to compression.", "partial", NODE153_EXACT_CONTINUATION_EVIDENCE),
    auditedObligation("XI-153-08", "For every supplied actual ordinary, decorated, or route-8 producer occurrence, route F4 on that identical occurrence and inherit its producer origin without rebuilding provenance.", "proved", NODE153_PRODUCED_SUPPORT_EVIDENCE),
    auditedObligation("XI-153-08-PRODUCERS", "Construct the complete graph-owned schedules of actual node-[64], node-[84], and node-[108] producer occurrences at the point where node [153] consumes them.", "missing"),
    auditedObligation("XI-153-09", "If the corridor terminates before the state bound, retain the whole actual path, exact run equation, F1/F4 negatives, and support bound.", "proved", NODE153_EXACT_CONTINUATION_EVIDENCE),
    auditedObligation("XI-153-10", "If a structural state repeats, retain the exact earlier/current prefix pair, span bound, universal F2, negative F3, exact run equation, and F1/F4 negatives.", "proved", NODE153_EXACT_CONTINUATION_EVIDENCE),
    auditedObligation("XI-153-11", "Prove terminal-or-repeated F5 exhaustiveness once F2 distinctions are excluded.", "proved", NODE153_EXACT_CONTINUATION_EVIDENCE),
    auditedObligation("XI-153-12", "From either F5 support construct the paper's two same-interface representatives, proper atom, boundary-profile equality, exact increment, finite response code/table, reflection, symbolic context coverage, and conditional silent orientation.", "missing"),
    auditedObligation("XI-153-13", "Show every surviving selected half-edge yields exactly one canonical germ incidence after only the named routed losses.", "missing"),
    auditedObligation("XI-153-14", "Prove the subcubic per-vertex multiplicity bound B_cold and per-germ intersection degree at most M_cold B_cold.", "missing"),
    auditedObligation("XI-153-15", "Greedily extract pairwise vertex-disjoint germs and prove N_germ >= b/D_cold-o(n), including the substitutions through 13C and theta-theta_win.", "missing"),
    auditedObligation("XI-153-16", "Account for work using only actual corridor stages, local states, response codes, and candidate supports.", "partial", STRUCTURAL_FRONTIER_EVIDENCE),
  ],
  154: [
    auditedObligation("XI-154-01", "Consume an actual node-[153] ColdBoundedGerm, not a caller-authored surrogate.", "missing"),
    auditedObligation("XI-154-02", "Separate equal-length germs to the finite same-interface table and orient a nonzero increment for length-changing germs.", "missing"),
    auditedObligation("XI-154-03", "Check literal hit first, then scan the exact finite local response codes for the first distinction, otherwise prove response neutrality.", "proved", NODE154_CLASSIFIER_EVIDENCE),
    auditedObligation("XI-154-04", "G1 retains the actual hit cycle and window offset.", "proved", NODE154_CLASSIFIER_EVIDENCE),
    auditedObligation("XI-154-05", "G2 constructs one literal compatible outside context distinguishing the representatives.", "proved", NODE154_CLASSIFIER_EVIDENCE),
    auditedObligation("XI-154-06", "G3 derives target completeness from symbolic coverage and builds the conditional silent exchange only after neutrality.", "proved", NODE154_CLASSIFIER_EVIDENCE),
    auditedObligation("XI-154-07", "Prove the three cases exhaustive with a local work/trace bound and no ambient context enumeration.", "proved", NODE154_CLASSIFIER_EVIDENCE),
  ],
  155: [
    auditedObligation("XI-155-01", "Consume the exact G1 constructor produced by node [154].", "missing"),
    auditedObligation("XI-155-02", "Execute the supplied-cycle CT1 on the identical graph and prove C1, trace, one check, and contradiction with target avoidance.", "proved", DYADIC_TERMINAL_EVIDENCE),
  ],
  156: [
    auditedObligation("XI-156-01", "Consume the exact G2 distinction from node [154].", "missing"),
    auditedObligation("XI-156-02", "Convert that literal distinction to the target-defective quotient on the same atom/replacement/context.", "proved"),
    auditedObligation("XI-156-03", "Route the defect to the exact named sparse-exit or exit-(4) ledger, preserving occurrence provenance.", "missing"),
  ],
  157: [
    auditedObligation("XI-157-01", "Consume the exact G3 silent exchange from node [154].", "missing"),
    auditedObligation("XI-157-02", "Build and execute the proper-support CT3 compression; prove terminal, trace, one check, totality, and minimality contradiction.", "proved"),
    auditedObligation("XI-157-03", "Consume every equal-length/short-exception same-interface table row and route realizing, distinguishing, handoff, and neutral rows exactly as the paper states.", "missing"),
    auditedObligation("XI-157-04", "For a neutral table row, construct a genuinely smaller proper representative rather than assuming it.", "missing"),
  ],
};

const a = (nodeId: number, label: string): ErdosProofNode => ({
  nodeId,
  kind: "assertion",
  label,
});

const d = (nodeId: number, label: string): ErdosProofNode => ({
  nodeId,
  kind: "decision",
  label,
});

const t = (nodeId: number, label: string): ErdosProofNode => ({
  nodeId,
  kind: "terminal",
  label,
});

const e = (
  source: number,
  target: number,
  label?: string,
  dashed = false,
): ErdosProofEdge => ({ source, target, label, dashed });

export const ERDOS_PROOF_FLOW_PARTS: ErdosProofPart[] = [
  {
    part: 1,
    roman: "I",
    title: "Counterexample reductions and the P₁₃ spine",
    summary: "Sets up a minimal counterexample, the target algebra, replacement machinery, induced-P₁₃ packing, and the first sparse/dense split.",
    nodes: [
      a(1, "finite simple graph G"),
      d(2, "counterexample? δ(G) ≥ 3 and no power-of-two cycle"),
      t(3, "not a counterexample"),
      a(4, "choose a lexicographically minimal counterexample"),
      a(5, "target algebra: every oriented edge has no Mersenne return"),
      d(6, "Mersenne return exists?"),
      t(7, "power-of-two cycle"),
      a(8, "no proper subgraph with minimum degree 3"),
      a(9, "edge-deletion critical; every edge touches a degree-3 vertex"),
      a(10, "vertices of degree at least 4 are independent"),
      a(11, "boundaried atoms and boundary degree profile"),
      a(12, "context universality for target-complete identifications"),
      a(13, "replacement lemma"),
      a(14, "hereditary target-uncompressibility of proper supports"),
      d(15, "G is P₁₃-free?"),
      t(16, "HSS theorem gives a target cycle"),
      a(17, "maximal disjoint induced-P₁₃ packing P"),
      a(18, "P₁₃ label algebra: 399 labels, safety relations, and curvature"),
      d(19, "non-near-cubic surplus? σ(G) > Csp √n"),
      a(20, "surplus-pair accounting branch"),
      a(21, "finite enumeration of curvature and P₁₃ constants"),
      d(22, "P₁₃ packing density too large?"),
      t(23, "P₁₃-window entropy overflow"),
      a(24, "window-density bound; sharper bound in the high-entropy branch"),
      a(25, "Residual A: a large, componentwise P₁₃-free remainder R"),
    ],
    edges: [
      e(1, 2), e(2, 3, "no"), e(2, 4, "yes"), e(4, 5), e(5, 6),
      e(6, 7, "yes"), e(6, 8, "no"), e(8, 9), e(9, 10), e(10, 11),
      e(11, 12), e(12, 13), e(13, 14), e(14, 15), e(15, 16, "yes"),
      e(15, 17, "no"), e(17, 18), e(18, 19), e(19, 20, "yes"),
      e(19, 21, "no"), e(21, 22), e(22, 23, "yes"), e(22, 24, "no"),
      e(24, 25),
    ],
    continuations: [
      { source: 20, target: 125, label: "expanded in Part X" },
      { source: 24, target: 145, label: "hot/cold interface in Part XI" },
      { source: 25, target: 26, label: "continues in Part II" },
    ],
  },
  {
    part: 2,
    roman: "II",
    title: "Residual deficiency and the rank split",
    summary: "Builds the remainder budget and separates rank-drop dependence from the full-curvature-rank residual.",
    nodes: [
      a(26, "Residual A: R is large and componentwise P₁₃-free"),
      a(27, "no component of R has an internal 3-core"),
      a(28, "positive deficiency def⁺(X)"),
      a(29, "external-incidence supply and surplus-adjusted deficiency bound"),
      a(30, "wedge lower bound, sharpened in the high-entropy branch"),
      a(31, "curvature target-rank rΩ(R)"),
      d(32, "rank drop?"),
      a(33, "Branch D: rank-reducing curvature dependence"),
      a(34, "Residual B: no rank drop; full curvature rank"),
    ],
    edges: [
      e(26, 27), e(27, 28), e(28, 29), e(29, 30), e(30, 31), e(31, 32),
      e(32, 33, "yes"), e(32, 34, "no"),
    ],
    continuations: [
      { source: 33, target: 35, label: "rank-drop branch in Part III" },
      { source: 34, target: 47, label: "full-rank branch in Part IV" },
    ],
  },
  {
    part: 3,
    roman: "III",
    title: "Rank-drop closure",
    summary: "Exhausts context failure, proper compression, support smearing, and whole-graph delocalization on the rank-drop branch.",
    nodes: [
      a(35, "Branch D: rank-reducing curvature dependence"),
      d(36, "valid against every outside context?"),
      t(37, "target-defective quotient"),
      d(38, "target-complete with a smaller proper representative?"),
      t(39, "proper atom compression"),
      a(40, "requires enlarged connected support Z ⊋ C"),
      d(41, "Z is a proper subgraph of G?"),
      t(42, "proper-support smearing closure: target defect or compression"),
      a(43, "Z = G: whole-graph delocalization"),
      a(44, "1–3 repair identity"),
      a(45, "target, replacement, or global-profile barrier"),
      t(46, "rank-drop branch closed"),
    ],
    edges: [
      e(35, 36), e(36, 37, "no"), e(36, 38, "yes"), e(38, 39, "yes"),
      e(38, 40, "no"), e(40, 41), e(41, 42, "yes"), e(41, 43, "no"),
      e(43, 44), e(44, 45), e(45, 46),
    ],
    continuations: [],
  },
  {
    part: 4,
    roman: "IV",
    title: "Full-rank curvature budget",
    summary: "Converts full curvature rank into a cost and entropy split, leaving the large-budget net-deficiency residual.",
    nodes: [
      a(47, "Residual B: full curvature rank"),
      a(48, "forced curvature cost; sharper high-entropy constant"),
      a(49, "per-vertex remainder entropy η(R)"),
      d(50, "remainder entropy at least one tenth log₂ n?"),
      a(51, "high-entropy remainder branch"),
      a(52, "window-plus-remainder accounting bounds the packing density"),
      d(53, "remaining non-curvature budget below the curvature cost?"),
      t(54, "entropy cap closes"),
      a(55, "Residual C: large-budget branch"),
      a(56, "net-deficiency cap below 1/4"),
    ],
    edges: [
      e(47, 48), e(48, 49), e(49, 50), e(50, 51, "yes"), e(51, 52),
      e(52, 54), e(50, 53, "no"), e(53, 54, "yes"), e(53, 55, "no"),
      e(55, 56),
    ],
    continuations: [{ source: 56, target: 57, label: "continues in Part V" }],
  },
  {
    part: 5,
    roman: "V",
    title: "Net-charge split",
    summary: "Localizes a negative connected piece and separates Type A from the high-degree-surplus Type B branch.",
    nodes: [
      a(57, "large-budget net cap"),
      a(58, "net charge N°"),
      d(59, "N°(R) ≥ 0?"),
      t(60, "net-cap contradiction"),
      a(61, "choose connected X with negative net charge"),
      d(62, "high-degree surplus?"),
      a(63, "Type A, continued in Part VIII"),
      a(64, "Type B, continued in Part VI"),
    ],
    edges: [
      e(57, 58), e(58, 59), e(59, 60, "yes"), e(59, 61, "no"), e(61, 62),
      e(62, 63, "no"), e(62, 64, "yes"),
    ],
    continuations: [
      { source: 63, target: 86, label: "Type A in Part VIII" },
      { source: 64, target: 65, label: "Type B in Part VI" },
    ],
  },
  {
    part: 6,
    roman: "VI",
    title: "Type B fan ledger",
    summary: "Runs the high-degree fan dichotomy, certificate and B2 ledgers, fan-mass accounting, and the route-8 continuation.",
    nodes: [
      a(65, "Type B assigned support: fan centers and decorated handoff data"),
      a(66, "Type A exit-7 input from the Part VIII handoff"),
      a(67, "high-degree centers independent; fan neighbours cubic"),
      d(68, "some center has degree greater than 4?"),
      a(69, "degree > 4 local dichotomy produces fan-closed ports"),
      a(70, "fan-safe and P₁₃-certificate graphs; marked degree cap 8"),
      d(71, "certificate labelling present?"),
      d(72, "local fan-window ledger complete and B2 disjointness holds?"),
      a(73, "B2 failure: minimal Type B overlap obstruction"),
      a(74, "B2 bridge reduction: nonnegative charge, saturated Type A, or bounded boundary overload"),
      a(75, "bridge fan-mass charged to assigned surplus"),
      a(76, "Type B cannot carry the linear deficit outside two-carrier route 8"),
      a(77, "route-8 cores continue in Part IX"),
    ],
    edges: [
      e(66, 65, undefined, true), e(65, 67), e(67, 68), e(68, 69, "yes"),
      e(68, 70, "no"), e(69, 70), e(70, 71), e(71, 72, "yes"),
      e(71, 75, "no"), e(72, 73, "no"), e(72, 74, "yes"), e(73, 75),
      e(74, 76), e(75, 76), e(76, 77),
    ],
    continuations: [
      { source: 68, target: 78, label: "degree-4 branch in Part VII" },
      { source: 77, target: 110, label: "route 8 in Part IX" },
    ],
  },
  {
    part: 7,
    roman: "VII",
    title: "Degree-four Type B branch",
    summary: "Expands the degree-four case into certificate-closed, B2-paid, overlap, and fan-mass alternatives.",
    nodes: [
      d(78, "degree-4 branch: dG(h) = 4"),
      a(79, "degree-4 fan profile with center surplus 1"),
      d(80, "certificate labelling present?"),
      d(81, "small closed count, or B2 disjoint ledger?"),
      a(82, "certificate-closed or B2-paid; nonnegative net charge outside route 8"),
      a(83, "B2 fails: minimal Type B overlap obstruction"),
      a(84, "selected-center and grouped fan-mass route"),
      a(85, "degree-4 Type B cannot carry linear deficit outside route 8"),
    ],
    edges: [
      e(78, 79, "no"), e(79, 80), e(80, 81, "yes"), e(80, 84, "no"),
      e(81, 82, "yes"), e(81, 83, "no"), e(83, 84), e(82, 85),
      e(84, 85),
    ],
    continuations: [{ source: 85, target: 77, label: "returns to the Part VI route-8 output" }],
  },
  {
    part: 8,
    roman: "VIII",
    title: "Type A exits",
    summary: "Applies the 3/7/11 charge bound and tests exits 1–7 before exposing the route-8 residual.",
    nodes: [
      a(86, "Type A: zero surplus and deficiency below |X|/4"),
      a(87, "P₁₃-free; bounded subcubic diameter and size"),
      a(88, "raw thresholds H₀ ≤ 4, H₁ ≤ 8, H₂ ≤ 12"),
      d(89, "some receiver is saturated?"),
      a(90, "unsaturated receiver loads"),
      a(91, "3/7/11 charge bound"),
      t(92, "unsaturated Type A charge closes"),
      d(93, "some port has four visible receiver-entry returns?"),
      a(94, "visible-first silent excess pays four times the Type A deficit"),
      d(95, "exit 1: Mersenne return?"),
      t(96, "target cycle"),
      d(97, "exit 2: power-of-two theta?"),
      t(98, "target cycle"),
      d(99, "exit 3: P₁₃ label collision?"),
      t(100, "label/target collision"),
      d(101, "exit 4: target-defective quotient?"),
      a(102, "target defect peels one load"),
      d(103, "exit 5: target-complete response compression?"),
      t(104, "uncompressibility contradiction"),
      d(105, "exit 6: proper/global delocalization?"),
      t(106, "delocalization branch closes"),
      d(107, "exit 7: decorated handoff fan?"),
      a(108, "return to the Type B handoff"),
      a(109, "route-8 residual continued in Part IX"),
    ],
    edges: [
      e(86, 87), e(87, 88), e(88, 89), e(89, 90, "no"), e(90, 91), e(91, 92),
      e(89, 93, "yes"), e(93, 95, "yes"), e(93, 94, "no"), e(94, 101),
      e(95, 96, "yes"), e(95, 97, "no"), e(97, 98, "yes"), e(97, 99, "no"),
      e(99, 100, "yes"), e(99, 101, "no"), e(101, 102, "yes"),
      e(102, 89, "recompute L₄"), e(101, 103, "no"), e(103, 104, "yes"),
      e(103, 105, "no"), e(105, 106, "yes"), e(105, 107, "no"),
      e(107, 108, "yes"), e(107, 109, "no"),
    ],
    continuations: [
      { source: 108, target: 66, label: "Type B handoff in Part VI" },
      { source: 109, target: 110, label: "route 8 in Part IX" },
    ],
  },
  {
    part: 9,
    roman: "IX",
    title: "Route-8 pressure closure",
    summary: "Extracts the route-8 burden, tests carrier-core sizes, and closes both the private-carrier and two-carrier branches.",
    nodes: [
      a(110, "exit 8: route-8 residual profile"),
      a(111, "global squeeze extracts a Type A collection carrying the deficit"),
      a(112, "route-8 basin burden dominates four times the deficit"),
      a(113, "large-budget deficit lower bound"),
      a(114, "pass each entry to its canonical minimal target-complete carrier core"),
      d(115, "some entry has at most one essential core?"),
      t(116, "one of exits 4–7 occurs"),
      d(117, "some entry has at most two carriers?"),
      a(118, "two-carrier route-8 entry"),
      a(119, "otherwise every indexed entry has three private essential carriers"),
      a(120, "private-carrier upper budget"),
      a(121, "burden-plus-deficit lower budget"),
      t(122, "numerical contradiction with the window threshold"),
      a(123, "large-budget pressure descent; target defects peel"),
      t(124, "local no-go theorem excludes two-carrier route-8 obstruction"),
    ],
    edges: [
      e(110, 111), e(111, 112), e(112, 113), e(113, 114), e(114, 115),
      e(115, 116, "yes"), e(115, 117, "no"), e(117, 118, "yes"),
      e(118, 123), e(123, 124), e(117, 119, "no"), e(119, 120),
      e(120, 121), e(121, 122),
    ],
    continuations: [],
  },
  {
    part: 10,
    roman: "X",
    title: "Sparse surplus accounting",
    summary: "Expands the non-near-cubic branch through active ports, canonical pairs, blocker ledgers, and geometric overload discharge.",
    nodes: [
      a(125, "sparse-pressure survivor after P₁₃ label algebra and sparse exits"),
      a(126, "sparse envelope and exact surplus identity"),
      a(127, "excess-port extraction: one active port per surplus unit"),
      a(128, "canonical activation: returns, open ports, and triangular response"),
      a(129, "full active family and baseline spine bound"),
      d(130, "canonical pair split: blocker-free?"),
      a(131, "free-pair entropy sandwich"),
      d(132, "blocked-pair routing: exit or canonical blocker?"),
      t(133, "sparse surplus exit closes"),
      a(134, "canonical blocker and capacity-token ledger"),
      a(135, "exact window-join pressure"),
      a(136, "tokenized blocked-pair ledger with three supply classes"),
      d(137, "coupled excess is positive?"),
      t(138, "no overload: explicit quadratic surplus bound and near-cubic spine"),
      d(139, "window-incidence token?"),
      a(140, "window-incidence geometric audit"),
      d(141, "remainder-surplus token?"),
      a(142, "remainder-surplus geometric audit"),
      a(143, "primitive-carrier geometric audit"),
      t(144, "bottleneck discharge: sparse exit, Type B, or near-cubic spine"),
    ],
    edges: [
      e(125, 126), e(126, 127), e(127, 128), e(128, 129), e(129, 130),
      e(130, 131, "yes"), e(130, 132, "no"), e(132, 133, "exit"),
      e(132, 134, "blocker"), e(134, 135), e(135, 136), e(136, 137),
      e(131, 137, "free pairs"), e(137, 138, "no"), e(137, 139, "yes"),
      e(139, 140, "yes"), e(139, 141, "no"), e(141, 142, "yes"),
      e(141, 143, "no"), e(140, 144, "bottleneck"), e(142, 144, "bottleneck"),
      e(143, 144, "bottleneck"),
    ],
    continuations: [
      { source: 138, target: 145, label: "near-cubic interface in Part XI" },
    ],
  },
  {
    part: 11,
    roman: "XI",
    title: "Hot/cold window interface",
    summary: "Audits the open near-cubic interface: nodes 151–152 are exact, while graph-owned entropy and cold-germ closure remain residuals.",
    nodes: [
      a(145, "hot/cold window interface after the spine estimate"),
      d(146, "cold-window density below 1/78?"),
      t(147, "route-8 private-carrier collision closes"),
      d(148, "live-hot entropy cap closes?"),
      t(149, "P₁₃-density cap"),
      a(150, "hot failure forces a linear cold-window mass"),
      a(151, "all but lower-order many cold windows are ambient-cubic"),
      a(152, "cold-window stub excess"),
      a(153, "canonical cold return: dyadic hit, surplus handoff, or ambient-finite structural germ"),
      d(154, "constant target-relative promotion available?"),
      t(155, "G1 endpoint after a constructed dyadic hit"),
      t(156, "G2 exact target-defect residual; closing consumer open"),
      t(157, "G3 compression after target-complete promotion; producer open"),
    ],
    edges: [
      e(145, 146), e(146, 147, "yes"), e(146, 148, "no"), e(148, 149, "yes"),
      e(148, 150, "no"), e(150, 151), e(151, 152), e(152, 153), e(153, 154),
      e(154, 155, "G1"), e(154, 156, "G2"), e(154, 157, "G3 / finite"),
    ],
    continuations: [],
  },
];

export const ERDOS_PROOF_FLOW_NODES = ERDOS_PROOF_FLOW_PARTS.flatMap(
  (part) => part.nodes,
);

export function proofFlowNodeElementId(nodeId: number): string {
  return `proof-node:${nodeId}`;
}

export function proofFlowNodeNumber(elementId: string): number | null {
  const match = /^proof-node:(\d+)$/.exec(elementId);
  return match ? Number(match[1]) : null;
}

export function proofFlowNodeSteps(
  manuscript: ExampleManuscript,
): Map<number, string[]> {
  const result = new Map<number, string[]>();
  for (const step of manuscript.proofSteps) {
    const nodeIds = new Set(step.manuscriptRefs.flatMap((reference) => reference.nodeIds));
    for (const nodeId of nodeIds) {
      result.set(nodeId, [...(result.get(nodeId) ?? []), step.stepId]);
    }
  }
  return result;
}

export function proofFlowNodeStatuses(
  manuscript: ExampleManuscript,
): Map<number, "implemented" | "partial" | "next" | "notStarted"> {
  const statuses = new Map<
    number,
    "implemented" | "partial" | "next" | "notStarted"
  >();
  const formalized = new Set(manuscript.formalizedNodeIds);
  // Any implemented evidence for an otherwise incomplete manuscript cell is
  // partial coverage, even when another proof step also marks that cell as the
  // next frontier.  This keeps genuine Lean progress yellow instead of letting
  // the frontier marker hide it.
  const priority = { notStarted: 0, next: 1, partial: 2, implemented: 3 } as const;
  for (const step of manuscript.proofSteps) {
    for (const reference of step.manuscriptRefs) {
      for (const nodeId of reference.nodeIds) {
        const audited = AUDITED_ERDOS_NODE_OBLIGATIONS[nodeId];
        const auditedComplete = audited !== undefined
          && audited.length > 0
          && audited.every((obligation) => obligation.status === "proved");
        const status = formalized.has(nodeId) || auditedComplete
          ? "implemented"
          : step.status === "implemented"
            ? "partial"
            : step.status;
        const previous = statuses.get(nodeId);
        if (!previous || priority[status] > priority[previous]) {
          statuses.set(nodeId, status);
        }
      }
    }
  }
  for (const nodeId of formalized) statuses.set(nodeId, "implemented");
  for (const [nodeId, obligations] of Object.entries(AUDITED_ERDOS_NODE_OBLIGATIONS)) {
    if (obligations.length > 0 && obligations.every((obligation) => obligation.status === "proved")) {
      statuses.set(Number(nodeId), "implemented");
    }
  }
  return statuses;
}

/**
 * Return the durable obligation ledger for one original manuscript cell.
 *
 * Declaration groups are evidence for a mathematical responsibility, not
 * separate responsibilities.  Green unaudited cells therefore collapse to
 * their one paper-cell contract, while yellow cells retain audited properties,
 * authored missing properties, and deduplicated proof-frontier limitations.
 * Thus the UI never upgrades a prose task merely because it appears here, and
 * inherited plumbing cannot inflate the obligation total.
 */
export function proofFlowNodeObligations(
  manuscript: ExampleManuscript,
  nodeId: number,
): readonly ErdosNodeObligation[] {
  const node = ERDOS_PROOF_FLOW_NODES.find((candidate) => candidate.nodeId === nodeId);
  if (!node) return [];

  // These property-level ledgers are the audited node contract. Do not append
  // synthetic cell/evidence rows: doing so would distort the task totals and
  // could hide an exact predecessor obligation behind unrelated local lemmas.
  const audited = AUDITED_ERDOS_NODE_OBLIGATIONS[nodeId];
  if (audited) return audited;

  const status = proofFlowNodeStatuses(manuscript).get(nodeId) ?? "notStarted";
  const formalized = new Set(manuscript.formalizedNodeIds);
  const referencedSteps = manuscript.proofSteps.filter((step) =>
    step.manuscriptRefs.some((reference) => reference.nodeIds.includes(nodeId)));
  const implementedSteps = referencedSteps.filter((step) =>
    step.status === "implemented" && step.declarationGroups.length > 0);
  const evidenceStepIds = implementedSteps.map((step) => step.stepId);
  const remaining = ORIGINAL_ERDOS_NODE_OBLIGATIONS[nodeId] ?? [];
  const cellStatus: ErdosNodeObligationStatus = status === "implemented"
    ? "proved"
    : evidenceStepIds.length
      ? "partial"
      : "missing";

  const cellResponsibility: ErdosNodeObligation = {
    obligationId: `node-${nodeId}-paper-cell`,
    title: "Original diagram-cell responsibility",
    statement: node.label,
    status: cellStatus,
    evidenceStepIds,
  };
  // Declaration groups explain evidence for the paper-cell responsibility;
  // they are not additional mathematical obligations.  Counting each group
  // here duplicated inherited provenance, runner, trace, and work theorems and
  // made the remaining-task total depend on how finely Lean evidence happened
  // to be documented.
  const outstandingSteps = referencedSteps
    .filter((step) => step.status !== "implemented")
    .map((step) => ({
      obligationId: `node-${nodeId}-step-${step.stepId}`,
      title: step.title,
      statement: step.scopeNotes || step.plainExplanation,
      status: "missing" as const,
      evidenceStepIds: [],
    }));

  const seenLimitations = new Set<string>();
  const inheritedLimitations = implementedSteps.flatMap((step) => {
    const statement = step.scopeNotes.trim();
    if (!statement || seenLimitations.has(statement)) return [];
    seenLimitations.add(statement);
    return [{
      obligationId: `node-${nodeId}-inherited-${step.stepId}`,
      title: "Inherited proof frontier",
      statement,
      status: "partial" as const,
      evidenceStepIds: [step.stepId],
    }];
  });

  if (formalized.has(nodeId)) return [cellResponsibility];
  const tasks = [...remaining, ...inheritedLimitations, ...outstandingSteps];
  return tasks.length ? tasks : [cellResponsibility];
}

/** Summarize the durable ledger without treating partial evidence as proved. */
export function proofFlowNodeObligationProgress(
  manuscript: ExampleManuscript,
  nodeId: number,
): ErdosNodeObligationProgress {
  const obligations = proofFlowNodeObligations(manuscript, nodeId);
  const proved = obligations.filter((obligation) => obligation.status === "proved").length;
  return {
    proved,
    total: obligations.length,
    remaining: obligations.length - proved,
  };
}

/**
 * Aggregate the same original-paper obligation ledgers displayed on each node.
 * Partial obligations remain unfinished: only fully proved tasks contribute to
 * the implemented count shown in the page-level progress bar.
 */
export function proofFlowObligationProgress(
  manuscript: ExampleManuscript,
): ErdosNodeObligationProgress {
  return ERDOS_PROOF_FLOW_NODES.reduce<ErdosNodeObligationProgress>(
    (progress, node) => {
      const nodeProgress = proofFlowNodeObligationProgress(manuscript, node.nodeId);
      return {
        proved: progress.proved + nodeProgress.proved,
        total: progress.total + nodeProgress.total,
        remaining: progress.remaining + nodeProgress.remaining,
      };
    },
    { proved: 0, total: 0, remaining: 0 },
  );
}

export function erdosProofFlowElements(
  part: ErdosProofPart,
  manuscript: ExampleManuscript,
): GraphElement[] {
  const statuses = proofFlowNodeStatuses(manuscript);
  const steps = proofFlowNodeSteps(manuscript);
  const continuationSources = new Set(part.continuations.map((continuation) => continuation.source));
  const nodes = part.nodes.map((node) => {
    const status = statuses.get(node.nodeId) ?? "notStarted";
    const obligationProgress = proofFlowNodeObligationProgress(manuscript, node.nodeId);
    const proofOrigin = "original";
    const unconditionallyClosed = status === "implemented"
      && node.kind === "terminal"
      && !continuationSources.has(node.nodeId);
    return {
      data: {
        id: proofFlowNodeElementId(node.nodeId),
        label: status === "partial"
          ? `[${node.nodeId}] ${node.label}\nObligations ${obligationProgress.proved}/${obligationProgress.total} · ${obligationProgress.remaining} left`
          : `[${node.nodeId}] ${node.label}`,
        kind: "proofFlowNode",
        proofNodeKind: node.kind,
        proofNodeId: node.nodeId,
        part: part.part,
        status,
        proofOrigin,
        verified: status === "implemented",
        closure: unconditionallyClosed ? "closed" : "open",
        proofStepIds: steps.get(node.nodeId) ?? [],
        obligationsProved: obligationProgress.proved,
        obligationsTotal: obligationProgress.total,
        obligationsRemaining: obligationProgress.remaining,
      },
    };
  });
  const edges = part.edges.map((edge, index) => ({
    data: {
      id: `proof-edge:${part.part}:${index + 1}`,
      source: proofFlowNodeElementId(edge.source),
      target: proofFlowNodeElementId(edge.target),
      label: edge.label ?? "",
      kind: "proofFlowEdge",
      dashed: edge.dashed ?? false,
    },
  }));
  return [...nodes, ...edges];
}
