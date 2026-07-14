import katex from "katex";
import { useMemo } from "react";

function removeOuterDelimiters(value: string): string {
  const source = value.trim();
  const delimiters: Array<[string, string]> = [
    ["$$", "$$"],
    ["\\[", "\\]"],
    ["\\(", "\\)"],
    ["$", "$"],
  ];

  for (const [opening, closing] of delimiters) {
    if (
      source.startsWith(opening)
      && source.endsWith(closing)
      && source.length > opening.length + closing.length
    ) {
      return source.slice(opening.length, -closing.length).trim();
    }
  }
  return source;
}

export function MathFormula({
  value,
  label,
  display = true,
}: {
  value: string;
  label: string;
  display?: boolean;
}) {
  const html = useMemo(
    () => katex.renderToString(removeOuterDelimiters(value), {
      displayMode: display,
      output: "htmlAndMathml",
      strict: "warn",
      throwOnError: false,
      trust: false,
    }),
    [display, value],
  );

  const properties = {
    className: display ? "math-formula" : "math-formula math-formula--inline",
    "aria-label": label,
    // KaTeX generates this markup with trust disabled, so user-provided TeX cannot
    // enable HTML commands or unsafe URLs.
    dangerouslySetInnerHTML: { __html: html },
  };
  return display ? <div {...properties} /> : <span {...properties} />;
}
