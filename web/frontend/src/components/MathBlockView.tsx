import katex from "katex";
import "katex/dist/katex.min.css";

import type { MathBlock } from "../v2-types";

export default function MathBlockView({ block }: { block: MathBlock }) {
  const formula = katex.renderToString(block.latex, {
    displayMode: block.display ?? true,
    output: "htmlAndMathml",
    strict: "warn",
    throwOnError: false,
    trust: false,
  });

  return (
    <figure className={block.display === false ? "math-block math-inline" : "math-block"}>
      <div dangerouslySetInnerHTML={{ __html: formula }} />
      {block.label ? <figcaption>{block.label}</figcaption> : null}
    </figure>
  );
}
