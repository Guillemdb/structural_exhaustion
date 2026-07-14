import { render, screen } from "@testing-library/react";
import { MemoryRouter } from "react-router-dom";
import { describe, expect, it, vi } from "vitest";

import { fetchExample } from "../api";
import type { ExampleResponse } from "../types";
import { ErdosGyarfasPage } from "./ErdosGyarfasPage";

vi.mock("../api", () => ({ fetchExample: vi.fn() }));
vi.mock("./ExamplePage", () => ({
  ExampleWorkspace: ({ mode }: { mode: string }) => <div>workspace:{mode}</div>,
}));

describe("ErdosGyarfasPage", () => {
  it("loads the compiled erdos-64 artifact into the dedicated workspace", async () => {
    vi.mocked(fetchExample).mockResolvedValue({} as ExampleResponse);
    render(<MemoryRouter><ErdosGyarfasPage /></MemoryRouter>);

    expect(await screen.findByText("workspace:erdos")).toBeVisible();
    expect(fetchExample).toHaveBeenCalledWith("erdos-64", expect.any(AbortSignal));
  });
});
