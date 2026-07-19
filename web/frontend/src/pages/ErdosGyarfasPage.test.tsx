import { render, screen } from "@testing-library/react";
import { MemoryRouter } from "react-router-dom";
import { describe, expect, it, vi } from "vitest";

import { fetchErdosProofHistory, fetchExample } from "../api";
import type { ErdosProofHistoryResponse, ExampleResponse } from "../types";
import { ErdosGyarfasPage } from "./ErdosGyarfasPage";

vi.mock("../api", () => ({ fetchExample: vi.fn(), fetchErdosProofHistory: vi.fn() }));
vi.mock("./ErdosLivingProofWorkspace", () => ({
  ErdosLivingProofWorkspace: ({ history }: { history: ErdosProofHistoryResponse | null }) => (
    <div>living-workspace:{history?.exampleId ?? "loading-history"}</div>
  ),
}));

describe("ErdosGyarfasPage", () => {
  it("loads the compiled erdos-64 artifact into the dedicated workspace", async () => {
    vi.mocked(fetchExample).mockResolvedValue({} as ExampleResponse);
    vi.mocked(fetchErdosProofHistory).mockResolvedValue({
      exampleId: "erdos-64",
    } as ErdosProofHistoryResponse);
    render(<MemoryRouter><ErdosGyarfasPage /></MemoryRouter>);

    expect(await screen.findByText("living-workspace:erdos-64")).toBeVisible();
    expect(fetchExample).toHaveBeenCalledWith("erdos-64", expect.any(AbortSignal));
    expect(fetchErdosProofHistory).toHaveBeenCalledWith(expect.any(AbortSignal));
  });
});
