import { readFileSync } from "node:fs";
import { resolve } from "node:path";

import katex from "katex";
import { describe, expect, it } from "vitest";

import type { ExampleDetail } from "../types";

function* objects(value: unknown): Generator<Record<string, unknown>> {
  if (Array.isArray(value)) {
    for (const child of value) yield* objects(child);
  } else if (value && typeof value === "object") {
    const record = value as Record<string, unknown>;
    yield record;
    for (const child of Object.values(record)) yield* objects(child);
  }
}

describe("generated Erdős manuscript artifact", () => {
  it("has one fragment per label and every current TeX formula renders in KaTeX", () => {
    const detail = JSON.parse(readFileSync(
      resolve(process.cwd(), "../../generated/examples/erdos-64.json"),
      "utf8",
    )) as ExampleDetail;
    const manuscript = detail.manuscript;
    expect(manuscript).not.toBeNull();
    if (!manuscript) return;

    const labels = new Set(manuscript.proofSteps.flatMap((step) =>
      step.manuscriptRefs.map((reference) => reference.label)));
    expect(new Set(manuscript.fragments.map((fragment) => fragment.label))).toEqual(labels);

    let mathCount = 0;
    for (const node of objects(manuscript.fragments)) {
      if (node.kind !== "math") continue;
      expect(typeof node.tex).toBe("string");
      katex.renderToString(node.tex as string, {
        displayMode: node.display === true,
        output: "htmlAndMathml",
        strict: "warn",
        throwOnError: true,
        trust: false,
      });
      mathCount += 1;
    }
    expect(mathCount).toBeGreaterThan(100);
  });
});
