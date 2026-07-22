import { fireEvent, render, screen, within } from "@testing-library/react";
import cytoscape from "cytoscape";
import { MemoryRouter } from "react-router-dom";
import { describe, expect, it, vi } from "vitest";

import GraphBlockView from "./GraphBlockView";

vi.mock("cytoscape", () => ({
  default: vi.fn(() => ({
    destroy: vi.fn(),
    getElementById: vi.fn(),
    on: vi.fn(),
  })),
}));

describe("GraphBlockView", () => {
  it("provides the legend and every directed, labelled edge without the canvas", () => {
    const { container } = render(
      <MemoryRouter>
        <GraphBlockView
          block={{
            kind: "graph",
            title: "Capability flow",
            nodes: [
              { id: "first", label: "First residual", x: 0, y: 0, kind: "residual" },
              { id: "second", label: "Second state", x: 100, y: 0, kind: "state" },
            ],
            edges: [
              { id: "edge", source: "first", target: "second", label: "requires" },
            ],
            legend: [
              { kind: "residual", label: "Residual" },
              { kind: "state", label: "Execution state" },
            ],
          }}
        />
      </MemoryRouter>,
    );

    expect(container.querySelector("details")).toHaveAttribute("open");
    expect(screen.getByRole("heading", { name: "Legend" })).toBeVisible();
    expect(screen.getByText("Execution state")).toBeVisible();
    const relationships = screen.getByRole("heading", { name: "Directed relationships" })
      .closest("section");
    expect(relationships).not.toBeNull();
    expect(within(relationships!).getByText("First residual")).toBeVisible();
    expect(within(relationships!).getByText("Second state")).toBeVisible();
    expect(within(relationships!).getByText("requires")).toBeVisible();

    const configuration = vi.mocked(cytoscape).mock.calls[0][0] as unknown as {
      style?: Array<{ selector?: string; style?: Record<string, unknown> }>;
    };
    const edgeStyle = configuration.style?.find((rule) => rule.selector === "edge");
    expect(edgeStyle).toMatchObject({ style: { label: "data(label)" } });
    expect(configuration.style).toContainEqual(expect.objectContaining({
      selector: 'node[kind = "residual"]',
      style: { "background-color": "#126f73" },
    }));
    expect(screen.getByText("Residual").previousElementSibling).toHaveAttribute(
      "data-node-kind",
      "residual",
    );
  });

  it("collapses a large complete index while keeping selected-node details visible", () => {
    const nodes = Array.from({ length: 41 }, (_, index) => ({
      id: `node-${index}`,
      label: `Node ${index}`,
      summary: index === 0 ? "Selected node summary" : `Summary ${index}`,
      x: index * 10,
      y: index % 2 === 0 ? 0 : 50,
      kind: "proof node",
    }));
    const edges = Array.from({ length: 40 }, (_, index) => ({
      id: `edge-${index}`,
      source: `node-${index}`,
      target: `node-${index + 1}`,
      label: `edge ${index + 1}`,
    }));
    const { container } = render(
      <MemoryRouter>
        <GraphBlockView block={{ kind: "graph", nodes, edges }} />
      </MemoryRouter>,
    );

    const details = container.querySelector("details");
    expect(details).not.toBeNull();
    expect(details).not.toHaveAttribute("open");
    expect(screen.getByText("Selected node summary")).toBeVisible();
    expect(screen.getByText("41 nodes · 40 directed relationships · expand for the complete keyboard and screen-reader index")).toBeVisible();

    const lastNodeControl = details!.querySelector(".graph-node-list li:last-child button");
    const lastEdge = within(details!).getByText("edge 40");
    expect(lastNodeControl).not.toBeVisible();
    expect(lastEdge).not.toBeVisible();

    fireEvent.click(within(details!).getByText("Accessible diagram index"));

    expect(details).toHaveAttribute("open");
    expect(lastNodeControl).toBeVisible();
    expect(lastEdge).toBeVisible();

    const configuration = vi.mocked(cytoscape).mock.calls.at(-1)?.[0] as unknown as {
      style?: Array<{ selector?: string; style?: Record<string, unknown> }>;
    };
    const edgeStyle = configuration.style?.find((rule) => rule.selector === "edge");
    expect(edgeStyle).toMatchObject({ style: { label: "" } });
    const nodeStyle = configuration.style?.find((rule) => rule.selector === "node");
    expect(nodeStyle).toMatchObject({ style: { label: "", height: 18, width: 18 } });
  });

  it("resets selection and the controlled index when the displayed block changes", () => {
    const firstBlock = {
      kind: "graph" as const,
      nodes: [
        { id: "one", label: "One", summary: "First summary", x: 0, y: 0 },
        { id: "two", label: "Two", summary: "Second summary", x: 100, y: 0 },
      ],
      edges: [],
    };
    const { container, rerender } = render(
      <MemoryRouter><GraphBlockView block={firstBlock} /></MemoryRouter>,
    );
    const details = container.querySelector("details");
    expect(details).toHaveAttribute("open");

    fireEvent.click(screen.getByRole("button", { name: "Two" }));
    expect(screen.getByText("Second summary")).toBeVisible();
    fireEvent.click(screen.getByText("Accessible diagram index"));
    expect(details).not.toHaveAttribute("open");

    rerender(
      <MemoryRouter>
        <GraphBlockView
          block={{
            kind: "graph",
            nodes: [{ id: "new", label: "New first", summary: "New summary", x: 0, y: 0 }],
            edges: [],
          }}
        />
      </MemoryRouter>,
    );

    expect(screen.getByText("New summary")).toBeVisible();
    expect(details).toHaveAttribute("open");
  });
});
