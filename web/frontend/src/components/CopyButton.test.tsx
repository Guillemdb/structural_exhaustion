import { fireEvent, render, screen, waitFor } from "@testing-library/react";
import { afterEach, describe, expect, it, vi } from "vitest";

import { CopyButton } from "./CopyButton";

const originalClipboard = Object.getOwnPropertyDescriptor(navigator, "clipboard");

function installClipboard(writeText: (text: string) => Promise<void>) {
  Object.defineProperty(navigator, "clipboard", {
    configurable: true,
    value: { writeText },
  });
}

afterEach(() => {
  if (originalClipboard) {
    Object.defineProperty(navigator, "clipboard", originalClipboard);
  } else {
    Reflect.deleteProperty(navigator, "clipboard");
  }
});

describe("CopyButton", () => {
  it("copies exact text and announces success", async () => {
    const writeText = vi.fn(() => Promise.resolve());
    installClipboard(writeText);
    render(<CopyButton text="#check Hypostructure.Core.Problem" label="Lean code" />);

    fireEvent.click(screen.getByRole("button", { name: "Copy Lean code" }));

    await waitFor(() => expect(writeText).toHaveBeenCalledWith(
      "#check Hypostructure.Core.Problem",
    ));
    expect(await screen.findByText("Copied")).toBeVisible();
    expect(screen.getByRole("status")).toHaveTextContent("Lean code copied to clipboard.");
  });

  it("shows and announces a clipboard failure", async () => {
    installClipboard(vi.fn(() => Promise.reject(new Error("denied"))));
    render(<CopyButton text="example" label="source excerpt" />);

    fireEvent.click(screen.getByRole("button", { name: "Copy source excerpt" }));

    expect(await screen.findByText("Copy failed")).toBeVisible();
    expect(screen.getByRole("status")).toHaveTextContent(
      "Could not copy source excerpt to the clipboard.",
    );
  });
});
