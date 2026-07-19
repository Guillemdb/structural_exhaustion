import { fireEvent, render, screen, waitFor } from "@testing-library/react";
import { MemoryRouter } from "react-router-dom";
import { describe, expect, it, vi } from "vitest";

import { fetchExamples } from "../api";
import type { ExamplesResponse } from "../types";
import { ExamplesPage } from "./ExamplesPage";

vi.mock("../api", () => ({ fetchExamples: vi.fn() }));

const response: ExamplesResponse = {
  artifactType: "frameworkExplorerExamples",
  artifactWarnings: [],
  catalog: {
    schemaVersion: "1.0.0",
    catalogHash: "1234567890abcdef",
    sourceOfTruth: { kind: "compiledLeanEnvironment" },
  },
  verification: {
    state: "verified",
    reportedStatus: "passed",
    exampleCatalogHash: "example-hash",
    verificationExampleCatalogHash: "example-hash",
    message: "Fresh example catalog.",
  },
  examples: [
    {
      exampleId: "even-cycle",
      title: "Even cycle",
      summary: "Combines activity and overload closure tactics.",
      proofStatus: "complete",
      tacticIds: ["CT6", "CT9", "CT1"],
      workflowCount: 2,
      workflows: [
        { workflowId: "main", title: "Main", purpose: "Prove the theorem.", completion: "complete" },
      ],
    },
    {
      exampleId: "erdos-64",
      title: "Erdős 6-4",
      summary: "A partial proof slice.",
      proofStatus: "partial",
      tacticIds: ["CT1", "CT2", "CT3"],
      workflowCount: 1,
      workflows: [
        { workflowId: "slice", title: "Slice", purpose: "Inspect the slice.", completion: "partial" },
      ],
    },
  ],
};

describe("ExamplesPage", () => {
  it("lists generated examples and filters by CT membership", async () => {
    vi.mocked(fetchExamples).mockResolvedValue(response);
    render(<MemoryRouter><ExamplesPage /></MemoryRouter>);

    expect(await screen.findByRole("heading", { name: "Even cycle" })).toBeVisible();
    expect(screen.queryByText("Erdős 6-4")).not.toBeInTheDocument();
    expect(screen.getByText("1 examples")).toBeVisible();

    fireEvent.change(screen.getByRole("searchbox", { name: "Search examples" }), {
      target: { value: "CT9" },
    });

    await waitFor(() => {
      expect(screen.getByRole("heading", { name: "Even cycle" })).toBeVisible();
      expect(screen.queryByText("Erdős 6-4")).not.toBeInTheDocument();
    });
    expect(screen.getByRole("link", { name: /Even cycle/ })).toHaveAttribute(
      "href",
      "/examples/even-cycle",
    );
  });

  it("shows stale generated-artifact warnings without replacing the page", async () => {
    vi.mocked(fetchExamples).mockResolvedValue({
      ...response,
      artifactWarnings: [
        {
          code: "staleHash",
          message: "The manuscript hash is stale. Showing embedded content.",
        },
      ],
    });
    render(<MemoryRouter><ExamplesPage /></MemoryRouter>);

    const warning = await screen.findByRole("status", {
      name: "Stale artifact warning",
    });
    expect(warning).toHaveTextContent("Generated content may be stale");
    expect(warning).toHaveTextContent("Showing embedded content");
    expect(screen.getByRole("heading", { name: "Even cycle" })).toBeVisible();
  });
});
