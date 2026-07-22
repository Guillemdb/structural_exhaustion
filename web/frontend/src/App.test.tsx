import { render, screen, waitFor } from "@testing-library/react";
import { MemoryRouter } from "react-router-dom";
import { afterEach, describe, expect, it, vi } from "vitest";

import App from "./App";
import type { PageView, SiteView } from "./v2-types";

const site: SiteView = {
  name: "Hypostructure",
  tagline: "Verified proof architecture",
  navigation: [
    { label: "Core", href: "/core" },
    { label: "Graph", href: "/graph" },
    { label: "PDE", href: "/pde" },
  ],
  snapshot: "test-snapshot",
  searchEnabled: true,
  verification: { state: "verified", label: "Verified", summary: "Kernel checked" },
};

function page(id: string, title: string): PageView {
  return {
    id,
    title,
    eyebrow: "Hypostructure",
    summary: "A ready-to-render view model supplied by Flask.",
    sections: [
      {
        id: "overview",
        title: "Overview",
        blocks: [{ kind: "callout", tone: "trust", title: "Kernel checked", body: "Fresh evidence." }],
      },
    ],
  };
}

function json(value: unknown, status = 200): Response {
  return new Response(JSON.stringify(value), {
    status,
    headers: { "Content-Type": "application/json" },
  });
}

afterEach(() => vi.unstubAllGlobals());

describe("Hypostructure application", () => {
  it("renders the home page from the v2 page endpoint", async () => {
    const fetchMock = vi.fn((input: RequestInfo | URL) => {
      const path = String(input);
      if (path === "/api/v2/site") return Promise.resolve(json(site));
      if (path === "/api/v2/pages/home") return Promise.resolve(json(page("home", "Proofs as typed programs")));
      return Promise.resolve(json({ title: "Not found" }, 404));
    });
    vi.stubGlobal("fetch", fetchMock);

    render(<MemoryRouter initialEntries={["/"]}><App /></MemoryRouter>);

    expect(await screen.findByRole("heading", { level: 1, name: "Proofs as typed programs" })).toBeVisible();
    expect(screen.getByRole("navigation", { name: "Main navigation" })).toBeVisible();
    expect(screen.getByText("Kernel checked")).toBeVisible();
    expect(fetchMock).toHaveBeenCalledWith("/api/v2/pages/home", expect.any(Object));
  });

  it("loads a CT detail without constructing CT data in the browser", async () => {
    const fetchMock = vi.fn((input: RequestInfo | URL) => {
      const path = String(input);
      if (path === "/api/v2/site") return Promise.resolve(json(site));
      if (path === "/api/v2/cts/CT7") return Promise.resolve(json(page("ct7", "CT7 · Exact context classification")));
      return Promise.resolve(json({ title: "Not found" }, 404));
    });
    vi.stubGlobal("fetch", fetchMock);

    render(<MemoryRouter initialEntries={["/core/cts/ct7"]}><App /></MemoryRouter>);

    expect(await screen.findByRole("heading", { level: 1, name: "CT7 · Exact context classification" })).toBeVisible();
    expect(fetchMock).toHaveBeenCalledWith("/api/v2/cts/CT7", expect.any(Object));
  });

  it("renders an allowlisted source excerpt inside the application", async () => {
    const fetchMock = vi.fn((input: RequestInfo | URL) => {
      const path = String(input);
      if (path === "/api/v2/site") return Promise.resolve(json(site));
      if (path === "/api/v2/sources/core-source/excerpt?start=2&end=3") {
        return Promise.resolve(json({
          sourceId: "core-source",
          path: "hypostructure/Hypostructure/Core/Problem.lean",
          sha256: "a".repeat(64),
          startLine: 2,
          endLine: 3,
          totalLines: 12,
          content: "structure Problem where\n  target : Nat",
        }));
      }
      return Promise.resolve(json({ title: "Not found" }, 404));
    });
    vi.stubGlobal("fetch", fetchMock);

    render(
      <MemoryRouter initialEntries={["/source/core-source?start=2&end=3"]}>
        <App />
      </MemoryRouter>,
    );

    expect(await screen.findByRole("heading", {
      level: 1,
      name: "hypostructure/Hypostructure/Core/Problem.lean",
    })).toBeVisible();
    expect(screen.getByText("structure Problem where")).toBeVisible();
    expect(screen.getByRole("button", { name: "Copy source excerpt" })).toBeVisible();
    expect(screen.getByRole("link", { name: "Next lines →" })).toHaveAttribute(
      "href",
      "/source/core-source?start=4&end=12",
    );
    expect(fetchMock).toHaveBeenCalledWith(
      "/api/v2/sources/core-source/excerpt?start=2&end=3",
      expect.any(Object),
    );
  });

  it("uses the backend site identity and respects disabled search", async () => {
    const configuredSite: SiteView = {
      ...site,
      name: "Configured Hypostructure",
      tagline: "Backend-owned proof documentation",
      searchEnabled: false,
    };
    const fetchMock = vi.fn((input: RequestInfo | URL) => {
      const path = String(input);
      if (path === "/api/v2/site") return Promise.resolve(json(configuredSite));
      if (path === "/api/v2/pages/home") return Promise.resolve(json(page("home", "Home")));
      return Promise.resolve(json({ title: "Not found" }, 404));
    });
    vi.stubGlobal("fetch", fetchMock);

    render(<MemoryRouter initialEntries={["/"]}><App /></MemoryRouter>);

    expect(await screen.findByRole("link", { name: "Configured Hypostructure home" })).toBeVisible();
    expect(screen.getAllByText("Backend-owned proof documentation").length).toBeGreaterThan(0);
    await waitFor(() => expect(screen.queryByRole("search")).not.toBeInTheDocument());
  });

  it("shows a real 404 for an unknown route", async () => {
    vi.stubGlobal("fetch", vi.fn(() => Promise.resolve(json(site))));
    render(<MemoryRouter initialEntries={["/old-framework"]}><App /></MemoryRouter>);
    expect(await screen.findByRole("heading", { name: "This route does not exist." })).toBeVisible();
    expect(screen.getByRole("link", { name: "Search the reference" })).toHaveAttribute("href", "/search");
  });

  it("announces the backend-ranked search result count", async () => {
    const fetchMock = vi.fn((input: RequestInfo | URL) => {
      const path = String(input);
      if (path === "/api/v2/site") return Promise.resolve(json(site));
      if (path === "/api/v2/search?q=routing") {
        return Promise.resolve(json({
          query: "routing",
          total: 2,
          page: 1,
          pageSize: 20,
          facets: [],
          results: [
            { id: "one", title: "First route", summary: "A route.", href: "/core/routes/one", kind: "route" },
            { id: "two", title: "Second route", summary: "Another route.", href: "/core/routes/two", kind: "route" },
          ],
        }));
      }
      return Promise.resolve(json({ title: "Not found" }, 404));
    });
    vi.stubGlobal("fetch", fetchMock);

    render(<MemoryRouter initialEntries={["/search?q=routing"]}><App /></MemoryRouter>);

    expect(await screen.findByText((_, element) => (
      element?.getAttribute("role") === "status"
      && element.textContent === "2 results for “routing”"
    ))).toHaveAttribute("aria-live", "polite");
  });
});
