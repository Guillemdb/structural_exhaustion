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

export function MathFormula({ value, label }: { value: string; label: string }) {
  const html = useMemo(
    () => katex.renderToString(removeOuterDelimiters(value), {
      displayMode: true,
      output: "htmlAndMathml",
      strict: "warn",
      throwOnError: false,
      trust: false,
    }),
    [value],
  );

  return (
    <div
      className="math-formula"
      aria-label={label}
      // KaTeX generates this markup with trust disabled, so user-provided TeX cannot
      // enable HTML commands or unsafe URLs.
      dangerouslySetInnerHTML={{ __html: html }}
    />
  );
}
