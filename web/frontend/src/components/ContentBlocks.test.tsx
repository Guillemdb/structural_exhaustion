import { render, screen } from "@testing-library/react";
import { MemoryRouter } from "react-router-dom";
import { describe, expect, it } from "vitest";

import type { ContentBlock } from "../v2-types";
import { ContentBlocks } from "./ContentBlocks";

function renderBlocks(blocks: ContentBlock[]) {
  return (
    <MemoryRouter>
      <ContentBlocks blocks={blocks} />
    </MemoryRouter>
  );
}

describe("ContentBlocks", () => {
  it("uses each card's stable identity when repeated titles are reordered", () => {
    const first = {
      title: "Shared capability",
      summary: "First contract.",
      href: "/reference/declarations/first",
    };
    const second = {
      title: "Shared capability",
      summary: "Second contract.",
      href: "/reference/declarations/second",
    };
    const block = (items: typeof first[]): ContentBlock[] => [{ kind: "cards", items }];
    const { container, rerender } = render(renderBlocks(block([first, second])));
    const firstCard = container.querySelector('a[href="/reference/declarations/first"]');

    rerender(renderBlocks(block([second, first])));

    expect(container.querySelector('a[href="/reference/declarations/first"]')).toBe(firstCard);
    expect(screen.getAllByRole("heading", { name: "Shared capability" })).toHaveLength(2);
  });

  it("renders structured callout items as a semantic list without requiring body text", () => {
    render(renderBlocks([{
      kind: "callout",
      tone: "info",
      title: "Author inputs",
      items: ["Define the problem.", "Provide the primitive hypothesis."],
    }]));

    const list = screen.getByRole("list");
    expect(list).toContainElement(screen.getByText("Define the problem."));
    expect(list).toContainElement(screen.getByText("Provide the primitive hypothesis."));
  });
});
