import { render, screen } from "@testing-library/react";
import { MemoryRouter, useLocation } from "react-router-dom";
import { describe, expect, it, vi } from "vitest";

import App from "./App";

vi.mock("./pages/FrameworkPage", () => ({ FrameworkPage: () => <div>framework</div> }));
vi.mock("./pages/TacticPage", () => ({ TacticPage: () => <div>tactic</div> }));
vi.mock("./pages/ExamplesPage", () => ({ ExamplesPage: () => <div>examples</div> }));
vi.mock("./pages/ExamplePage", () => ({ ExamplePage: () => <div>generic example</div> }));
vi.mock("./pages/ErdosGyarfasPage", () => ({
  ErdosGyarfasPage: () => <div>EG workspace</div>,
}));

function LocationProbe() {
  return <output aria-label="Current location">{useLocation().pathname}</output>;
}

describe("application routes", () => {
  it("redirects the legacy Erdős example route to its dedicated section", async () => {
    render(
      <MemoryRouter initialEntries={["/examples/erdos-64"]}>
        <App />
        <LocationProbe />
      </MemoryRouter>,
    );

    expect(await screen.findByText("EG workspace")).toBeVisible();
    expect(screen.getByRole("status", { name: "Current location" })).toHaveTextContent(
      "/erdos-gyarfas",
    );
  });

  it("keeps ordinary examples on the generic reader", () => {
    render(
      <MemoryRouter initialEntries={["/examples/even-cycle"]}>
        <App />
      </MemoryRouter>,
    );
    expect(screen.getByText("generic example")).toBeVisible();
  });
});
