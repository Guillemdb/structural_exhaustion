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
      a(84, "fan-mass route charges certificate and B2 failures"),
      a(85, "degree-4 Type B cannot carry linear deficit outside route 8"),
    ],
    edges: [
      e(78, 79, "no"), e(79, 80), e(80, 81, "yes"), e(80, 84, "no"),
      e(81, 82, "yes"), e(81, 83, "no"), e(83, 84), e(82, 85), e(84, 85),
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
      { source: 144, target: 65, label: "Type B outcome returns to Part VI" },
    ],
  },
  {
    part: 11,
    roman: "XI",
    title: "Hot/cold window interface",
    summary: "Closes the near-cubic interface via route-8 collision, a density cap, or the bounded cold-germ trichotomy.",
    nodes: [
      a(145, "hot/cold window interface after the spine estimate"),
      d(146, "cold-window density below 1/78?"),
      t(147, "route-8 private-carrier collision closes"),
      d(148, "live-hot entropy cap closes?"),
      t(149, "P₁₃-density cap"),
      a(150, "hot failure forces a linear cold-window mass"),
      a(151, "all but lower-order many cold windows are ambient-cubic"),
      a(152, "cold-window stub excess"),
      a(153, "first-failure extraction gives many disjoint bounded germs"),
      d(154, "bounded germ case?"),
      t(155, "G1: dyadic cycle"),
      t(156, "G2: target defect, exit 4, or handoff"),
      t(157, "G3 or same-interface table: compression"),
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
  const priority = { notStarted: 0, partial: 1, next: 2, implemented: 3 } as const;
  for (const step of manuscript.proofSteps) {
    for (const reference of step.manuscriptRefs) {
      for (const nodeId of reference.nodeIds) {
        const status = formalized.has(nodeId)
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
  return statuses;
}

export function erdosProofFlowElements(
  part: ErdosProofPart,
  manuscript: ExampleManuscript,
): GraphElement[] {
  const statuses = proofFlowNodeStatuses(manuscript);
  const steps = proofFlowNodeSteps(manuscript);
  const nodes = part.nodes.map((node) => {
    const status = statuses.get(node.nodeId) ?? "notStarted";
    return {
      data: {
        id: proofFlowNodeElementId(node.nodeId),
        label: `[${node.nodeId}] ${node.label}`,
        kind: "proofFlowNode",
        proofNodeKind: node.kind,
        proofNodeId: node.nodeId,
        part: part.part,
        status,
        verified: status === "implemented",
        proofStepIds: steps.get(node.nodeId) ?? [],
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
