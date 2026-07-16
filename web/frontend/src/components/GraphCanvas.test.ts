import cytoscape from "cytoscape";
import { describe, expect, it } from "vitest";

import { graphStyles } from "./GraphCanvas";

describe("GraphCanvas proof-flow colors", () => {
  it("distinguishes verified terminal closures from other implemented nodes", () => {
    const graph = cytoscape({
      headless: true,
      styleEnabled: true,
      style: graphStyles,
      elements: [
        {
          data: {
            id: "paper",
            label: "Paper only",
            kind: "proofFlowNode",
            status: "notStarted",
            verified: false,
          },
        },
        {
          data: {
            id: "partial",
            label: "Partially formalized",
            kind: "proofFlowNode",
            status: "partial",
            verified: false,
          },
        },
        {
          data: {
            id: "frontier",
            label: "Frontier",
            kind: "proofFlowNode",
            status: "next",
            verified: false,
          },
        },
        {
          data: {
            id: "implemented",
            label: "Implemented",
            kind: "proofFlowNode",
            status: "implemented",
            verified: true,
          },
        },
        {
          data: {
            id: "closed",
            label: "Unconditionally closed",
            kind: "proofFlowNode",
            proofNodeKind: "terminal",
            status: "implemented",
            verified: true,
            closure: "closed",
          },
        },
      ],
    });

    expect(graph.$id("paper").style("background-color")).toBe("rgb(251,250,246)");
    expect(graph.$id("partial").style("background-color")).toBe("rgb(226,189,63)");
    expect(graph.$id("frontier").style("background-color")).toBe("rgb(209,138,44)");
    expect(graph.$id("implemented").style("background-color")).toBe("rgb(57,122,80)");
    expect(graph.$id("closed").style("background-color")).toBe("rgb(23,107,67)");
    graph.destroy();
  });
});
