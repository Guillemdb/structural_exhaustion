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
  mode: "framework" | "machine" | "example";
  entryId?: string;
  selectedId?: string | null;
  onSelect?: (element: SelectedGraphElement | null) => void;
}

const graphStyles: cytoscape.StylesheetJson = [
  {
    selector: "node",
    style: {
      "background-color": "#315d73",
      "border-color": "#f9f7f1",
      "border-width": 3,
      color: "#172235",
      "font-family": "Inter, ui-sans-serif, system-ui, sans-serif",
      "font-size": 11,
      "font-weight": 650,
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
    selector: 'node[kind = "routedTactic"]',
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
    selector: 'edge[kind = "route"]',
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
    selector: [
      'edge[kind = "registeredRoute"]',
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
    selector: 'edge[kind = "registeredRoute"]',
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
            spacingFactor: mode === "example" ? 1.65 : 1.35,
            padding: 48,
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
            ? "Registered routes between closure tactics"
            : mode === "example"
              ? "Composition diagram for the selected example workflow"
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
