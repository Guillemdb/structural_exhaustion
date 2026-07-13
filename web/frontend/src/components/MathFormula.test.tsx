import { render } from "@testing-library/react";
import { describe, expect, it } from "vitest";

import { MathFormula } from "./MathFormula";

describe("MathFormula", () => {
  it("accepts raw TeX and common outer delimiters", () => {
    const raw = render(<MathFormula value="x^2" label="Raw formula" />);
    const delimited = render(<MathFormula value={"\\[x^2\\]"} label="Delimited formula" />);

    expect(raw.container.querySelector("math")).not.toBeNull();
    expect(delimited.container.querySelector("math")).not.toBeNull();
  });

  it("keeps trusted HTML commands and unsafe links disabled", () => {
    const { container } = render(
      <MathFormula
        value={"\\href{javascript:alert(1)}{x} + \\text{<script>alert(1)</script>}"}
        label="Untrusted formula"
      />,
    );

    expect(container.querySelector("a")).toBeNull();
    expect(container.querySelector("script")).toBeNull();
  });
});
