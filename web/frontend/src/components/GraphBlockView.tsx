import cytoscape, { type Core } from "cytoscape";
import { useEffect, useId, useLayoutEffect, useRef, useState } from "react";

import type { GraphBlock } from "../v2-types";
import { SmartLink } from "./SmartLink";

const LARGE_GRAPH_INDEX_SIZE = 80;

export default function GraphBlockView({ block }: { block: GraphBlock }) {
  const container = useRef<HTMLDivElement>(null);
  const accessibleIndex = useRef<HTMLDetailsElement>(null);
  const graph = useRef<Core | null>(null);
  const isLargeGraph = block.nodes.length + block.edges.length > LARGE_GRAPH_INDEX_SIZE;
  const [selected, setSelected] = useState(block.nodes[0]?.id ?? "");
  const relationshipsHeadingId = useId();
  const legendHeadingId = useId();
  const nodeLabels = new Map(block.nodes.map((node) => [node.id, node.label]));

  useEffect(() => {
    setSelected(block.nodes[0]?.id ?? "");
  }, [block]);

  useLayoutEffect(() => {
    if (accessibleIndex.current) accessibleIndex.current.open = !isLargeGraph;
  }, [block, isLargeGraph]);

  useEffect(() => {
    if (!container.current) return;
    graph.current = cytoscape({
      container: container.current,
      elements: [
        ...block.nodes.map((node) => ({
          data: { id: node.id, label: node.label, kind: node.kind ?? "stage" },
          position: { x: node.x, y: node.y },
        })),
        ...block.edges.map((edge) => ({
          data: {
            id: edge.id,
            source: edge.source,
            target: edge.target,
            label: edge.label ?? "",
          },
        })),
      ],
      layout: { name: "preset", fit: true, padding: 48 },
      minZoom: 0.35,
      maxZoom: 2.5,
      style: [
        {
          selector: "node",
          style: {
            "background-color": "#123f45",
            "border-color": "#d7a84b",
            "border-width": isLargeGraph ? 1.25 : 2,
            color: "#f8f3e8",
            label: isLargeGraph ? "" : "data(label)",
            "font-size": 11,
            "font-weight": 600,
            height: isLargeGraph ? 18 : 44,
            width: isLargeGraph ? 18 : 44,
            "text-valign": "center",
            "text-wrap": "wrap",
            "text-max-width": "80px",
          },
        },
        {
          selector: "node:selected",
          style: { "border-color": "#f0bd55", "border-width": isLargeGraph ? 3 : 5 },
        },
        {
          selector: 'node[kind = "application"]',
          style: { "background-color": "#7a3e62" },
        },
        {
          selector: 'node[kind = "domain"]',
          style: { "background-color": "#285f86" },
        },
        {
          selector: 'node[kind = "execution"]',
          style: { "background-color": "#236b5c" },
        },
        {
          selector: 'node[kind = "routing"]',
          style: { "background-color": "#775719" },
        },
        {
          selector: 'node[kind = "state"]',
          style: { "background-color": "#474f83" },
        },
        {
          selector: 'node[kind = "terminal"]',
          style: { "background-color": "#873f35" },
        },
        {
          selector: 'node[kind = "residual"]',
          style: { "background-color": "#126f73" },
        },
        {
          selector: 'node[kind = "proof node"]',
          style: { "background-color": "#514b7f" },
        },
        {
          selector: "edge",
          style: {
            "curve-style": "bezier",
            "line-color": "#8ea5a2",
            "target-arrow-color": "#8ea5a2",
            "target-arrow-shape": "triangle",
            color: "#41575a",
            label: isLargeGraph ? "" : "data(label)",
            "font-size": 9,
            "font-weight": 600,
            "text-background-color": "#edf0e9",
            "text-background-opacity": 0.95,
            "text-background-padding": "3px",
            "text-margin-y": -7,
            "text-rotation": "autorotate",
            width: isLargeGraph ? 1 : 1.5,
          },
        },
      ],
    });
    graph.current.on("select", "node", (event) => setSelected(event.target.id()));
    return () => {
      graph.current?.destroy();
      graph.current = null;
    };
  }, [block, isLargeGraph]);

  const selectedNode = block.nodes.find((node) => node.id === selected);

  return (
    <figure className="graph-figure">
      {block.title ? <h3>{block.title}</h3> : null}
      {block.description ? <p>{block.description}</p> : null}
      <div className="graph-canvas" ref={container} aria-hidden="true" />
      <figcaption>
        {selectedNode ? (
          <div className="graph-selection" aria-live="polite">
            <strong>{selectedNode.label}</strong>
            {selectedNode.summary ? <p>{selectedNode.summary}</p> : null}
            {selectedNode.href ? <SmartLink href={selectedNode.href}>Open details →</SmartLink> : null}
          </div>
        ) : null}
        <details
          ref={accessibleIndex}
          className="graph-accessible-index"
        >
          <summary>
            <strong>Accessible diagram index</strong>
            <span>
              {block.nodes.length} nodes · {block.edges.length} directed relationships
              {isLargeGraph ? " · expand for the complete keyboard and screen-reader index" : ""}
            </span>
          </summary>
          <div className="graph-accessible-index-body">
            <div className="graph-keyboard-heading">
              <strong>Nodes</strong>
              <span>Select a node to inspect it above and focus it in the diagram.</span>
            </div>
            <ul className="graph-node-list">
              {block.nodes.map((node) => (
                <li key={node.id}>
                  <button
                    type="button"
                    aria-pressed={selected === node.id}
                    onClick={() => {
                      setSelected(node.id);
                      const element = graph.current?.getElementById(node.id);
                      element?.select();
                      if (element) {
                        if (window.matchMedia?.("(prefers-reduced-motion: reduce)").matches) {
                          graph.current?.center(element);
                        } else {
                          graph.current?.animate({ center: { eles: element }, duration: 180 });
                        }
                      }
                    }}
                  >
                    <span>{node.label}</span>
                    {node.kind ? <small>{node.kind}</small> : null}
                  </button>
                </li>
              ))}
            </ul>
            {block.legend && block.legend.length > 0 ? (
              <section className="graph-legend" aria-labelledby={legendHeadingId}>
                <h4 id={legendHeadingId}>Legend</h4>
                <ul>
                  {block.legend.map((item) => (
                    <li key={`${item.kind}-${item.label}`}>
                      <span className="graph-legend-swatch" data-node-kind={item.kind} aria-hidden="true" />
                      <span>{item.label}</span>
                      <code>{item.kind}</code>
                    </li>
                  ))}
                </ul>
              </section>
            ) : null}
            <section className="graph-relationships" aria-labelledby={relationshipsHeadingId}>
              <h4 id={relationshipsHeadingId}>Directed relationships</h4>
              {block.edges.length > 0 ? (
                <ul>
                  {block.edges.map((edge) => (
                    <li key={edge.id}>
                      <span>{nodeLabels.get(edge.source) ?? edge.source}</span>
                      <span className="graph-edge-arrow" aria-hidden="true">→</span>
                      <span className="sr-only"> leads to </span>
                      <span>{nodeLabels.get(edge.target) ?? edge.target}</span>
                      <small>{edge.label || "Unlabelled transition"}</small>
                    </li>
                  ))}
                </ul>
              ) : (
                <p>This diagram has no directed relationships.</p>
              )}
            </section>
          </div>
        </details>
      </figcaption>
    </figure>
  );
}
