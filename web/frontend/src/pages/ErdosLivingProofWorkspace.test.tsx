import { readFileSync } from "node:fs";
import { resolve } from "node:path";

import { fireEvent, render, screen, within } from "@testing-library/react";
import { MemoryRouter } from "react-router-dom";
import { describe, expect, it, vi } from "vitest";

import type {
  ErdosProofHistoryResponse,
  ExampleDetail,
  ExampleResponse,
} from "../types";
import { ErdosLivingProofWorkspace } from "./ErdosLivingProofWorkspace";

vi.mock("../components/ErdosProofFlowDiagram", () => ({
  ErdosProofFlowDiagram: ({ activeNodeId }: { activeNodeId: number | null }) => (
    <div data-testid="proof-diagram">diagram node {activeNodeId}</div>
  ),
}));

vi.mock("../components/LeanSourceViewer", () => ({
  LeanSourceViewer: ({ proofStep }: { proofStep?: { title: string } }) => (
    <div data-testid="source-companion">source {proofStep?.title ?? "none"}</div>
  ),
}));

function generatedResponse(): ExampleResponse {
  const example = JSON.parse(readFileSync(
    resolve(process.cwd(), "../../generated/examples/erdos-64.json"),
    "utf8",
  )) as ExampleDetail;
  example.sourceOfTruth.descriptorSource = {
    path: "examples/erdos_64_eg/Erdos64EG/WebExport.lean",
    sha256: "a".repeat(64),
  };
  return {
    artifactType: "frameworkExplorerExample",
    artifactWarnings: [],
    catalogHash: "catalog",
    frameworkCatalogHash: "framework",
    verification: {
      state: "verified",
      reportedStatus: "passed",
      exampleCatalogHash: "catalog",
      verificationExampleCatalogHash: "catalog",
      message: "Fresh compiled artifact.",
    },
    example,
    tactics: [],
  };
}

function generatedHistory(): ErdosProofHistoryResponse {
  const history = JSON.parse(readFileSync(
    resolve(process.cwd(), "../../generated/examples/erdos-64-history.json"),
    "utf8",
  )) as Omit<ErdosProofHistoryResponse, "artifactType" | "artifactWarnings"> & {
    artifactType: "erdosProofHistory";
  };
  return {
    ...history,
    artifactType: "frameworkExplorerErdosProofHistory",
    artifactWarnings: [],
  };
}

describe("ErdosLivingProofWorkspace", () => {
  it("navigates proof status, causal evidence, impact, history, and reading contract", () => {
    render(
      <MemoryRouter>
        <ErdosLivingProofWorkspace
          response={generatedResponse()}
          history={generatedHistory()}
        />
      </MemoryRouter>,
    );

    expect(screen.getByRole("heading", { name: "Erdős–Gyárfás Problem 64" })).toBeVisible();
    expect(screen.getByText("56/157")).toBeVisible();
    expect(screen.getByText("Fresh compiled descriptor")).toBeVisible();

    fireEvent.change(screen.getByPlaceholderText("e.g. rank, CT15, node 31"), {
      target: { value: "curvature target-rank" },
    });
    const index = screen.getByLabelText("Search and filter paper nodes");
    fireEvent.click(within(index).getByRole("button", { name: /curvature target-rank/i }));
    expect(screen.getByRole("heading", { name: "Paper node [31]" })).toBeVisible();
    expect(screen.getByTestId("proof-diagram")).toHaveTextContent("diagram node 31");

    fireEvent.click(screen.getByRole("button", { name: "Framework impact" }));
    expect(screen.getByRole("heading", { name: "What the framework contributes" })).toBeVisible();
    expect(screen.getByText(/evidence of reuse, not a percentage/i)).toBeVisible();

    fireEvent.click(screen.getByRole("button", { name: "Implementation history" }));
    expect(screen.getByRole("heading", { name: "Living implementation history" })).toBeVisible();
    expect(screen.getByText("Latest recorded artifact")).toBeVisible();

    fireEvent.click(screen.getByRole("button", { name: "How to read this" }));
    expect(screen.getByRole("heading", { name: "How to read this living proof" })).toBeVisible();
    expect(screen.getByRole("heading", { name: "Audit the speedup claim through reuse" })).toBeVisible();
  });
});
