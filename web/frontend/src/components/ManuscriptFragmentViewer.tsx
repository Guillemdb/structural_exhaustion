import { useEffect, useMemo, useState } from "react";

import type {
  ExampleManuscript,
  ExampleManuscriptBlock,
  ExampleManuscriptInline,
  ExampleProofStep,
} from "../types";
import { MathFormula } from "./MathFormula";

function ManuscriptInlines({
  inlines,
  keyPrefix,
}: {
  inlines: ExampleManuscriptInline[];
  keyPrefix: string;
}) {
  return inlines.map((inline, index) => {
    const key = `${keyPrefix}-${index}`;
    switch (inline.kind) {
      case "text":
        return <span key={key}>{inline.text}</span>;
      case "space":
      case "softBreak":
        return <span key={key}> </span>;
      case "lineBreak":
        return <br key={key} />;
      case "code":
        return <code key={key}>{inline.text}</code>;
      case "math":
        return (
          <MathFormula
            value={inline.tex}
            label={inline.display ? "Displayed manuscript equation" : "Inline manuscript equation"}
            display={inline.display}
            key={key}
          />
        );
      case "reference":
        return (
          <span
            className="manuscript-reference"
            title={inline.labels.join(", ")}
            data-labels={inline.labels.join(",")}
            key={key}
          >
            {inline.prefix ? `${inline.prefix} ` : ""}{inline.text}
          </span>
        );
      case "citation":
        return <span className="manuscript-citation" title={inline.keys.join(", ")} key={key}>{inline.text}</span>;
      case "emphasis":
        return <em key={key}><ManuscriptInlines inlines={inline.children} keyPrefix={key} /></em>;
      case "strong":
        return <strong key={key}><ManuscriptInlines inlines={inline.children} keyPrefix={key} /></strong>;
      case "underline":
        return <u key={key}><ManuscriptInlines inlines={inline.children} keyPrefix={key} /></u>;
      case "strikeout":
        return <s key={key}><ManuscriptInlines inlines={inline.children} keyPrefix={key} /></s>;
      case "smallCaps":
        return <span className="manuscript-small-caps" key={key}><ManuscriptInlines inlines={inline.children} keyPrefix={key} /></span>;
      case "upright":
        return <span className="manuscript-upright" key={key}><ManuscriptInlines inlines={inline.children} keyPrefix={key} /></span>;
    }
  });
}

function ManuscriptFigure({ block }: { block: Extract<ExampleManuscriptBlock, { kind: "figure" }> }) {
  const source = useMemo(
    () => `data:image/svg+xml;charset=utf-8,${encodeURIComponent(block.svg)}`,
    [block.svg],
  );
  return (
    <figure className="manuscript-figure" data-label={block.label}>
      <img src={source} alt={`${block.label} manuscript diagram`} />
      <figcaption><ManuscriptBlocks blocks={block.caption} keyPrefix={`${block.label}-caption`} /></figcaption>
    </figure>
  );
}

function ManuscriptBlockView({
  block,
  blockKey,
}: {
  block: ExampleManuscriptBlock;
  blockKey: string;
}) {
  switch (block.kind) {
    case "paragraph":
      return <p><ManuscriptInlines inlines={block.inlines} keyPrefix={blockKey} /></p>;
    case "heading":
      return (
        <h2 className="manuscript-heading" data-level={block.level} id={block.label ?? undefined}>
          <ManuscriptInlines inlines={block.inlines} keyPrefix={blockKey} />
        </h2>
      );
    case "environment":
      return (
        <section
          className={`manuscript-environment manuscript-environment--${block.environment}`}
          data-label={block.label ?? undefined}
        >
          {block.title ? (
            <header className="manuscript-environment-title">
              <span>{block.environment}</span>{" "}
              (<ManuscriptInlines inlines={block.title} keyPrefix={`${blockKey}-title`} />)
            </header>
          ) : null}
          <ManuscriptBlocks blocks={block.blocks} keyPrefix={blockKey} />
        </section>
      );
    case "orderedList":
      return (
        <ol start={block.start}>
          {block.items.map((item, index) => (
            <li key={`${blockKey}-item-${index}`}>
              <ManuscriptBlocks blocks={item} keyPrefix={`${blockKey}-item-${index}`} />
            </li>
          ))}
        </ol>
      );
    case "bulletList":
      return (
        <ul>
          {block.items.map((item, index) => (
            <li key={`${blockKey}-item-${index}`}>
              <ManuscriptBlocks blocks={item} keyPrefix={`${blockKey}-item-${index}`} />
            </li>
          ))}
        </ul>
      );
    case "blockQuote":
      return <blockquote><ManuscriptBlocks blocks={block.blocks} keyPrefix={blockKey} /></blockquote>;
    case "codeBlock":
      return <pre><code>{block.text}</code></pre>;
    case "figure":
      return <ManuscriptFigure block={block} />;
  }
}

function ManuscriptBlocks({
  blocks,
  keyPrefix,
}: {
  blocks: ExampleManuscriptBlock[];
  keyPrefix: string;
}) {
  return blocks.map((block, index) => {
    const blockKey = `${keyPrefix}-block-${index}`;
    return <ManuscriptBlockView block={block} blockKey={blockKey} key={blockKey} />;
  });
}

export function ManuscriptFragmentViewer({
  manuscript,
  proofStep,
}: {
  manuscript: ExampleManuscript;
  proofStep?: ExampleProofStep;
}) {
  const references = proofStep?.manuscriptRefs ?? [];
  const [activeLabel, setActiveLabel] = useState(references[0]?.label ?? "");

  useEffect(() => {
    setActiveLabel(references[0]?.label ?? "");
  }, [proofStep?.stepId]);

  const fragment = manuscript.fragments.find((candidate) => candidate.label === activeLabel);
  const activeReference = references.find((reference) => reference.label === activeLabel);

  return (
    <>
      <div className="manuscript-label-tabs" aria-label="Manuscript labels">
        {references.length ? references.map((reference) => (
          <button
            type="button"
            className={reference.label === activeLabel ? "is-active" : ""}
            onClick={() => setActiveLabel(reference.label)}
            title={reference.label}
            key={reference.label}
          >
            <span>{reference.title}</span>
            <code>{reference.label}</code>
          </button>
        )) : <span>No manuscript label is assigned to this selection.</span>}
      </div>
      <div className="manuscript-fragment" role="region" aria-label="Rendered manuscript fragment">
        {fragment ? (
          <article>
            <header>
              <span className="eyebrow">{fragment.environment}</span>
              <strong>{activeReference?.title ?? fragment.label}</strong>
              <code>{fragment.label}</code>
              <small>
                line {fragment.sourceLine}
                {fragment.includesProof ? " · statement and proof" : " · labeled content"}
              </small>
            </header>
            <ManuscriptBlocks blocks={fragment.blocks} keyPrefix={fragment.label} />
          </article>
        ) : references.length ? (
          <div className="manuscript-empty">The generated fragment for this label is unavailable.</div>
        ) : (
          <div className="manuscript-empty">
            This implementation-support selection has no corresponding manuscript fragment.
          </div>
        )}
      </div>
    </>
  );
}
