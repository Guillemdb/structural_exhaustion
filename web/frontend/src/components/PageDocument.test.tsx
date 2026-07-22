import { render, screen } from "@testing-library/react";
import { MemoryRouter } from "react-router-dom";
import { describe, expect, it } from "vitest";

import { PageDocument } from "./PageDocument";

describe("PageDocument", () => {
  it("renders backend-composed cards, tables, code, and trust evidence", () => {
    render(
      <MemoryRouter>
        <PageDocument
          page={{
            id: "core",
            title: "Core",
            summary: "The shared proof substrate.",
            breadcrumbs: [{ label: "Home", href: "/" }, { label: "Core" }],
            verification: { state: "verified", label: "Verified snapshot", summary: "Fresh source evidence" },
            sections: [
              {
                id: "contracts",
                title: "Typed contracts",
                blocks: [
                  { kind: "cards", items: [{ title: "Residual", summary: "Literal predecessor state.", href: "/reference/declarations/residual" }] },
                  { kind: "table", caption: "Ownership", columns: [{ key: "owner", label: "Owner" }], rows: [{ owner: "Core" }] },
                  {
                    kind: "code",
                    language: "lean",
                    caption: "Compiled fixture",
                    code: "#check Hypostructure.Core.Problem",
                    sourceHref: "/api/v2/sources/core-problem/excerpt?start=4&end=8",
                  },
                ],
              },
            ],
          }}
        />
      </MemoryRouter>,
    );

    expect(screen.getByRole("heading", { level: 1, name: "Core" })).toBeVisible();
    expect(screen.getByRole("link", { name: /Residual/ })).toHaveAttribute("href", "/reference/declarations/residual");
    expect(screen.getByRole("table", { name: "Ownership" })).toBeVisible();
    expect(screen.getByText("#check Hypostructure.Core.Problem")).toBeVisible();
    expect(screen.getByRole("button", { name: "Copy lean code" })).toBeVisible();
    expect(screen.getByRole("link", { name: "View source ↗" })).toHaveAttribute(
      "href",
      "/source/core-problem?start=4&end=8",
    );
    expect(screen.getByText("Verified snapshot")).toBeVisible();
  });
});
