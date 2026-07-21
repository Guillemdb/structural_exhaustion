import cytoscape, {
  type Core,
  type ElementDefinition,
  type EventObject,
  type LayoutOptions,
} from "cytoscape";
import { useEffect, useRef } from "react";

import type { GraphElement, GraphElementData, SelectedGraphElement } from "../types";

interface GraphCanvasProps {
  elements: GraphElement[];
  mode: "framework" | "machine" | "internals" | "example" | "proofFlow";
  entryId?: string;
  selectedId?: string | null;
  onSelect?: (element: SelectedGraphElement | null) => void;
}

export const graphStyles: cytoscape.StylesheetJson = [
  {
    selector: "node",
    style: {
      "background-color": "#315d73",
      "border-color": "#f9f7f1",
      "border-width": 3,
      color: "#172235",
      "font-family": "Inter, ui-sans-serif, system-ui, sans-serif",
      "font-size": 11,
      "font-weight": "bold",
      label: "data(label)",
      "text-background-color": "#fbfaf6",
      "text-background-opacity": 0.92,
      "text-background-padding": "4px",
      "text-border-color": "#e5e0d4",
      "text-border-opacity": 1,
      "text-border-width": 1,
      "text-halign": "center",
      "text-margin-y": 28,
      "text-max-width": "150px",
      "text-wrap": "wrap",
      height: 28,
      width: 28,
    },
  },
  {
    selector: 'node[kind = "tactic"]',
    style: {
      "background-color": "#193f57",
      height: 52,
      shape: "round-rectangle",
      width: 70,
      "text-margin-y": 0,
      "text-valign": "center",
      color: "#ffffff",
      "text-background-opacity": 0,
      "text-border-width": 0,
      "font-size": 14,
    },
  },
  {
    selector: 'node[kind = "transitionTargetTactic"]',
    style: {
      "background-color": "#755d91",
      "border-color": "#e8dff0",
      "border-style": "dashed",
      color: "#ffffff",
      "font-size": 12,
      height: 58,
      label: "data(label)",
      shape: "round-rectangle",
      "text-background-opacity": 0,
      "text-border-width": 0,
      "text-margin-y": 0,
      "text-valign": "center",
      width: 94,
    },
  },
  {
    selector: 'node[kind = "entry"]',
    style: { "background-color": "#1c7c73", shape: "ellipse" },
  },
  {
    selector: 'node[kind = "decision"]',
    style: { "background-color": "#d18a2c", shape: "diamond" },
  },
  {
    selector: 'node[kind = "residual"]',
    style: { "background-color": "#b6534f", shape: "diamond" },
  },
  {
    selector: 'node[kind = "certificate"]',
    style: { "background-color": "#4d815f", shape: "round-rectangle" },
  },
  {
    selector: 'node[kind = "certification"]',
    style: { "background-color": "#4c7588", shape: "hexagon" },
  },
  {
    selector: 'node[kind = "definition"]',
    style: { "background-color": "#697889", shape: "rectangle" },
  },
  {
    selector: 'node[kind = "loop"]',
    style: { "background-color": "#755d91", shape: "round-hexagon" },
  },
  {
    selector: "node[expanded]",
    style: {
      "background-color": "#f3f0e8",
      "background-opacity": 0.82,
      "border-color": "#315d73",
      "border-style": "dashed",
      "border-width": 2,
      color: "#193f57",
      label: "data(label)",
      padding: "28px",
      shape: "round-rectangle",
      "text-background-opacity": 0,
      "text-border-width": 0,
      "text-halign": "center",
      "text-margin-y": 0,
      "text-valign": "top",
    },
  },
  {
    selector: 'node[kind = "internalStep"]',
    style: {
      "background-color": "#315d73",
      "border-width": 2,
      color: "#172235",
      height: 34,
      label: "data(label)",
      shape: "round-rectangle",
      "text-margin-y": 32,
      "text-max-width": "130px",
      width: 54,
    },
  },
  {
    selector: 'node[kind = "internalStep"][role = "authorObject"]',
    style: { "background-color": "#d18a2c" },
  },
  {
    selector: 'node[kind = "internalStep"][role = "inferredInstance"]',
    style: { "background-color": "#697889" },
  },
  {
    selector: 'node[kind = "internalStep"][role = "predecessorState"]',
    style: { "background-color": "#755d91" },
  },
  {
    selector: 'node[kind = "internalStep"][role = "theorem"]',
    style: { "background-color": "#193f57", shape: "hexagon" },
  },
  {
    selector: 'node[kind = "internalStep"][role = "output"]',
    style: { "background-color": "#4d815f" },
  },
  {
    selector: 'node[kind = "leanDeclaration"], node[kind = "externalDeclaration"]',
    style: {
      "background-color": "#fbfaf6",
      "border-color": "#7b8d95",
      "border-width": 2,
      color: "#334753",
      height: 26,
      shape: "rectangle",
      "text-margin-y": 28,
      "text-max-width": "120px",
      width: 34,
    },
  },
  {
    selector: 'node[kind = "externalDeclaration"]',
    style: {
      "border-style": "dotted",
      opacity: 0.72,
    },
  },
  {
    selector: 'node[kind = "problem"]',
    style: { "background-color": "#315d73", shape: "round-rectangle" },
  },
  {
    selector: 'node[kind = "adapter"]',
    style: { "background-color": "#d18a2c", shape: "hexagon" },
  },
  {
    selector: 'node[kind = "theorem"]',
    style: { "background-color": "#193f57", shape: "round-rectangle" },
  },
  {
    selector: 'node[kind = "fixture"]',
    style: { "background-color": "#697889", shape: "rectangle" },
  },
  {
    selector: 'node[kind = "proofFlowNode"]',
    style: {
      "background-color": "#fbfaf6",
      "border-color": "#87969a",
      "border-width": 2,
      color: "#263b46",
      "font-size": 10,
      "font-weight": "bold",
      height: 62,
      shape: "round-rectangle",
      "text-background-opacity": 0,
      "text-border-width": 0,
      "text-margin-y": 0,
      "text-max-width": "180px",
      "text-valign": "center",
      width: 210,
    },
  },
  {
    selector: 'node[kind = "proofFlowNode"][status = "notStarted"]',
    style: {
      "background-color": "#fbfaf6",
      "border-color": "#87969a",
      color: "#263b46",
    },
  },
  {
    selector: 'node[kind = "proofFlowNode"][proofNodeKind = "decision"]',
    style: {
      height: 94,
      shape: "diamond",
      "text-max-width": "132px",
      width: 198,
    },
  },
  {
    selector: 'node[kind = "proofFlowNode"][proofNodeKind = "terminal"]',
    style: {
      height: 68,
      shape: "ellipse",
      "text-max-width": "155px",
      width: 190,
    },
  },
  {
    selector: 'node[kind = "proofFlowNode"][status = "implemented"]',
    style: {
      "background-color": "#397a50",
      "border-color": "#cfe5d5",
      color: "#ffffff",
    },
  },
  {
    selector: 'node[kind = "proofFlowNode"][status = "implemented"][closure = "closed"]',
    style: {
      "background-color": "#176b43",
      "border-color": "#9fd6b7",
      color: "#ffffff",
    },
  },
  {
    selector: 'node[kind = "proofFlowNode"][status = "partial"]',
    style: {
      "background-color": "#e2bd3f",
      "border-color": "#f3e3a4",
      color: "#3f3210",
      height: 82,
    },
  },
  {
    selector: 'node[kind = "proofFlowNode"][status = "next"]',
    style: {
      "background-color": "#d18a2c",
      "border-color": "#f5d198",
      "border-width": 3,
      color: "#ffffff",
    },
  },
  {
    selector: "edge",
    style: {
      width: 2,
      "line-color": "#9ba9ad",
      "target-arrow-color": "#9ba9ad",
      "target-arrow-shape": "triangle",
      "arrow-scale": 0.8,
      "curve-style": "bezier",
    },
  },
  {
    selector: 'edge[kind = "ctTransition"]',
    style: {
      color: "#52636b",
      "font-size": 8,
      label: "data(label)",
      "line-color": "#7c9098",
      "target-arrow-color": "#7c9098",
      "text-background-color": "#fdfcf9",
      "text-background-opacity": 0.94,
      "text-background-padding": "2px",
      "text-rotation": "autorotate",
    },
  },
  {
    selector: 'edge[kind = "transitionProfile"]',
    style: {
      width: 2.5,
      "line-color": "#755d91",
      "target-arrow-color": "#755d91",
      "line-style": "dashed",
      label: "data(label)",
      color: "#54406e",
      "font-size": 10,
      "text-background-color": "#fbfaf6",
      "text-background-opacity": 0.95,
      "text-background-padding": "3px",
      "text-rotation": "autorotate",
    },
  },
  {
    selector: 'edge[kind = "implementedTransition"]',
    style: {
      width: 3,
      "line-color": "#d18a2c",
      "target-arrow-color": "#d18a2c",
      label: "data(label)",
      color: "#7a521f",
      "font-size": 9,
      "text-background-color": "#fbfaf6",
      "text-background-opacity": 0.96,
      "text-background-padding": "3px",
      "text-rotation": "autorotate",
    },
  },
  {
    selector: [
      'edge[kind = "implementedTransition"][relationshipKind = "registeredRoute"]',
      'edge[kind = "implementedTransition"][relationshipKind = "registeredTransition"]',
    ].join(", "),
    style: {
      "line-color": "#755d91",
      "target-arrow-color": "#755d91",
      color: "#54406e",
    },
  },
  {
    selector: 'edge[kind = "implementedTransition"][relationshipKind = "scheduleAudit"]',
    style: {
      "line-color": "#697889",
      "target-arrow-color": "#697889",
      "line-style": "dotted",
      color: "#56646f",
    },
  },
  {
    selector: [
      'edge[kind = "registeredRoute"]',
      'edge[kind = "registeredTransition"]',
      'edge[kind = "frameworkComposition"]',
      'edge[kind = "proofData"]',
      'edge[kind = "validation"]',
      'edge[kind = "scheduleAudit"]',
      'edge[kind = "sharedProblem"]',
    ].join(", "),
    style: {
      label: "data(label)",
      color: "#56646f",
      "font-size": 9,
      "text-background-color": "#fbfaf6",
      "text-background-opacity": 0.95,
      "text-background-padding": "3px",
      "text-rotation": "autorotate",
    },
  },
  {
    selector: 'edge[kind = "registeredRoute"], edge[kind = "registeredTransition"]',
    style: {
      width: 3,
      "line-color": "#755d91",
      "target-arrow-color": "#755d91",
      label: "data(label)",
      color: "#54406e",
      "font-size": 9,
      "text-background-color": "#fbfaf6",
      "text-background-opacity": 0.95,
      "text-background-padding": "3px",
      "text-rotation": "autorotate",
    },
  },
  {
    selector: 'edge[kind = "frameworkComposition"]',
    style: {
      "line-color": "#d18a2c",
      "target-arrow-color": "#d18a2c",
    },
  },
  {
    selector: 'edge[kind = "validation"]',
    style: {
      "line-color": "#4d815f",
      "target-arrow-color": "#4d815f",
      "line-style": "dashed",
    },
  },
  {
    selector: 'edge[kind = "scheduleAudit"], edge[kind = "sharedProblem"]',
    style: {
      "line-color": "#697889",
      "target-arrow-color": "#697889",
      "line-style": "dotted",
    },
  },
  {
    selector: 'edge[kind = "proofData"]',
    style: {
      "line-color": "#1c7c73",
      "target-arrow-color": "#1c7c73",
    },
  },
  {
    selector: 'edge[kind = "proofFlowEdge"]',
    style: {
      color: "#55686f",
      "curve-style": "taxi",
      "font-size": 9,
      label: "data(label)",
      "line-color": "#71868d",
      "target-arrow-color": "#71868d",
      "text-background-color": "#fdfcf9",
      "text-background-opacity": 0.96,
      "text-background-padding": "3px",
      "text-rotation": "none",
      width: 2,
    },
  },
  {
    selector: 'edge[kind = "proofFlowEdge"][?dashed]',
    style: { "line-style": "dashed" },
  },
  {
    selector: 'edge[kind = "internalFlow"]',
    style: {
      color: "#596b74",
      "font-size": 8,
      label: "data(label)",
      "line-color": "#7b8d95",
      "target-arrow-color": "#7b8d95",
      "text-background-color": "#fdfcf9",
      "text-background-opacity": 0.9,
      "text-rotation": "autorotate",
    },
  },
  {
    selector: 'edge[kind = "typeDependency"], edge[kind = "bodyDependency"]',
    style: {
      color: "#6c5a43",
      "font-size": 8,
      label: "data(label)",
      "line-color": "#b58d57",
      "line-style": "dashed",
      "target-arrow-color": "#b58d57",
      "text-background-color": "#fdfcf9",
      "text-background-opacity": 0.9,
      "text-rotation": "autorotate",
      width: 1.5,
    },
  },
  {
    selector: ":selected",
    style: {
      "border-color": "#e0a33d",
      "border-width": 5,
      "line-color": "#e0a33d",
      "target-arrow-color": "#e0a33d",
      "z-index": 20,
    },
  },
];

export function GraphCanvas({
  elements,
  mode,
  entryId,
  selectedId,
  onSelect,
}: GraphCanvasProps) {
  const containerRef = useRef<HTMLDivElement>(null);
  const graphRef = useRef<Core | null>(null);
  const onSelectRef = useRef(onSelect);

  useEffect(() => {
    onSelectRef.current = onSelect;
  }, [onSelect]);

  useEffect(() => {
    if (!containerRef.current) return;
    const layout: LayoutOptions =
      mode === "framework"
        ? { name: "grid", cols: 5, padding: 42, avoidOverlap: true }
        : {
            name: "breadthfirst",
            directed: true,
            spacingFactor: mode === "example"
              ? 1.65
              : mode === "internals"
                ? 1.5
                : mode === "proofFlow"
                  ? 1.08
                  : 1.35,
            padding: mode === "proofFlow" ? 34 : 48,
            avoidOverlap: true,
          };
    const graph = cytoscape({
      container: containerRef.current,
      elements: elements as ElementDefinition[],
      style: graphStyles,
      layout,
      minZoom: 0.25,
      maxZoom: 2.4,
      wheelSensitivity: 0.22,
      selectionType: "single",
      boxSelectionEnabled: false,
    });
    graphRef.current = graph;

    graph.on("tap", "node, edge", (event: EventObject) => {
      const target = event.target;
      onSelectRef.current?.({
        id: target.id(),
        group: target.isNode() ? "node" : "edge",
        data: target.data() as GraphElementData,
      });
    });
    graph.on("tap", (event: EventObject) => {
      if (event.target === graph) onSelectRef.current?.(null);
    });

    return () => {
      graph.destroy();
      graphRef.current = null;
    };
  }, [elements, entryId, mode]);

  useEffect(() => {
    const graph = graphRef.current;
    if (!graph) return;
    graph.elements().unselect();
    if (selectedId) graph.getElementById(selectedId).select();
  }, [selectedId]);

  return (
    <div className="graph-shell">
      <div
        className={`graph-canvas graph-canvas--${mode}`}
        ref={containerRef}
        role="img"
        aria-label={
          mode === "framework"
            ? "Registered transition profiles and implemented proof transitions between closure tactics"
            : mode === "example"
              ? "Composition diagram for the selected example workflow"
              : mode === "proofFlow"
                ? "Selected part of the Chapter 1 proof dependency diagram"
              : mode === "internals"
                ? "Closure tactic graph with one node expanded into Lean internals"
              : "Closure tactic flow diagram"
        }
      />
      <div className="graph-controls" aria-label="Graph view controls">
        <button type="button" onClick={() => graphRef.current?.zoom(graphRef.current.zoom() * 1.2)}>
          +
        </button>
        <button type="button" onClick={() => graphRef.current?.zoom(graphRef.current.zoom() / 1.2)}>
          −
        </button>
        <button type="button" onClick={() => graphRef.current?.fit(undefined, 42)}>
          Fit
        </button>
      </div>
    </div>
  );
}
