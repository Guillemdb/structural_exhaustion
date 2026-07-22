import { lazy, Suspense } from "react";

import type { CardView, ContentBlock } from "../v2-types";
import { CopyButton } from "./CopyButton";
import { SmartLink } from "./SmartLink";

const GraphBlockView = lazy(() => import("./GraphBlockView"));
const MathBlockView = lazy(() => import("./MathBlockView"));

function Prose({ html }: { html: string }) {
  return <div className="prose" dangerouslySetInnerHTML={{ __html: html }} />;
}

function cardKey(item: CardView) {
  return ["card", item.href, item.title, item.summary, item.eyebrow, item.meta]
    .map((part) => part ?? "")
    .join("\u001f");
}

export function ContentBlocks({ blocks }: { blocks: ContentBlock[] }) {
  return (
    <>
      {blocks.map((block, index) => {
        const key = `${block.kind}-${index}`;
        switch (block.kind) {
          case "prose":
            return <Prose key={key} html={block.html} />;
          case "cards":
            return (
              <div key={key} className={`card-grid columns-${block.columns ?? 3}`}>
                {block.items.map((item) => {
                  const body = (
                    <>
                      {item.eyebrow ? <span className="eyebrow">{item.eyebrow}</span> : null}
                      <h3>{item.title}</h3>
                      <p>{item.summary}</p>
                      {item.meta ? <small>{item.meta}</small> : null}
                      {item.href ? <span className="card-arrow" aria-hidden="true">↗</span> : null}
                    </>
                  );
                  return item.href ? (
                    <SmartLink className="content-card" href={item.href} key={cardKey(item)}>
                      {body}
                    </SmartLink>
                  ) : (
                    <article className="content-card" key={cardKey(item)}>
                      {body}
                    </article>
                  );
                })}
              </div>
            );
          case "callout":
            return (
              <aside key={key} className={`callout callout-${block.tone}`}>
                <span className="callout-mark" aria-hidden="true">
                  {block.tone === "trust" ? "✓" : "i"}
                </span>
                <div>
                  <strong>{block.title}</strong>
                  {block.body ? <p>{block.body}</p> : null}
                  {block.items?.length ? (
                    <ul>
                      {block.items.map((item, itemIndex) => (
                        <li key={`${item}-${itemIndex}`}>{item}</li>
                      ))}
                    </ul>
                  ) : null}
                </div>
              </aside>
            );
          case "steps":
            return (
              <ol key={key} className="steps">
                {block.items.map((item) => (
                  <li key={item.title}>
                    <div>
                      <h3>{item.title}</h3>
                      <p>{item.body}</p>
                      {item.href ? <SmartLink href={item.href}>Continue →</SmartLink> : null}
                    </div>
                  </li>
                ))}
              </ol>
            );
          case "code":
            return (
              <figure key={key} className="code-block">
                <figcaption>
                  <span>{block.caption ?? block.language}</span>
                  <span className="code-actions">
                    {block.sourceHref ? <SmartLink href={block.sourceHref}>View source ↗</SmartLink> : null}
                    <CopyButton text={block.code} label={`${block.language} code`} />
                  </span>
                </figcaption>
                <pre tabIndex={0}>
                  <code>{block.code}</code>
                </pre>
              </figure>
            );
          case "math":
            return (
              <Suspense key={key} fallback={<div className="math-loading">Loading formula…</div>}>
                <MathBlockView block={block} />
              </Suspense>
            );
          case "table":
            return (
              <div key={key} className="table-scroll" tabIndex={0}>
                <table>
                  {block.caption ? <caption>{block.caption}</caption> : null}
                  <thead>
                    <tr>
                      {block.columns.map((column) => <th key={column.key} scope="col">{column.label}</th>)}
                    </tr>
                  </thead>
                  <tbody>
                    {block.rows.map((row, rowIndex) => (
                      <tr key={rowIndex}>
                        {block.columns.map((column) => <td key={column.key}>{String(row[column.key] ?? "—")}</td>)}
                      </tr>
                    ))}
                  </tbody>
                </table>
              </div>
            );
          case "graph":
            return (
              <Suspense key={key} fallback={<div className="graph-loading">Loading diagram…</div>}>
                <GraphBlockView block={block} />
              </Suspense>
            );
          case "links":
            return (
              <ul key={key} className="link-list">
                {block.items.map((item) => (
                  <li key={item.href}>
                    <SmartLink href={item.href}>
                      <strong>{item.label}</strong>
                      {item.description ? <span>{item.description}</span> : null}
                      <span aria-hidden="true">↗</span>
                    </SmartLink>
                  </li>
                ))}
              </ul>
            );
          case "stats":
            return (
              <dl key={key} className="metric-grid">
                {block.items.map((item) => (
                  <div key={item.label}>
                    <dt>{item.label}</dt>
                    <dd>{item.value}</dd>
                    {item.detail ? <small>{item.detail}</small> : null}
                  </div>
                ))}
              </dl>
            );
        }
      })}
    </>
  );
}
