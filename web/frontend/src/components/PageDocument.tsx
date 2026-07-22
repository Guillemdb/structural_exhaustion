import { Link } from "react-router-dom";

import { useDocumentMetadata } from "../hooks/useDocumentMetadata";
import type { PageView } from "../v2-types";
import { ContentBlocks } from "./ContentBlocks";

export function PageDocument({ page }: { page: PageView }) {
  useDocumentMetadata(page.title, page.summary, page.canonicalPath);

  return (
    <article className={`page page-${page.id}`}>
      <header className="page-hero">
        <div className="hero-orbit orbit-one" aria-hidden="true" />
        <div className="hero-orbit orbit-two" aria-hidden="true" />
        <div className="hero-content">
          {page.breadcrumbs?.length ? (
            <nav className="breadcrumbs" aria-label="Breadcrumb">
              <ol>
                {page.breadcrumbs.map((item, index) => (
                  <li key={`${item.label}-${index}`}>
                    {item.href ? <Link to={item.href}>{item.label}</Link> : <span aria-current="page">{item.label}</span>}
                  </li>
                ))}
              </ol>
            </nav>
          ) : null}
          {page.eyebrow ? <p className="hero-eyebrow">{page.eyebrow}</p> : null}
          <h1>{page.title}</h1>
          <p className="hero-summary">{page.summary}</p>
          {page.description ? <p className="hero-description">{page.description}</p> : null}
          {page.metrics?.length ? (
            <dl className="hero-metrics">
              {page.metrics.map((metric) => (
                <div key={metric.label}>
                  <dt>{metric.label}</dt>
                  <dd>{metric.value}</dd>
                  {metric.detail ? <small>{metric.detail}</small> : null}
                </div>
              ))}
            </dl>
          ) : null}
        </div>
      </header>
      <div className="page-body">
        {page.verification ? (
          <details className={`verification verification-${page.verification.state}`}>
            <summary>
              <span aria-hidden="true">{page.verification.state === "verified" ? "✓" : "!"}</span>
              <strong>{page.verification.label}</strong>
              <span>{page.verification.summary}</span>
            </summary>
            {page.verification.details?.length ? (
              <dl>
                {page.verification.details.map((detail) => (
                  <div key={detail.label}><dt>{detail.label}</dt><dd>{detail.value}</dd></div>
                ))}
              </dl>
            ) : null}
          </details>
        ) : null}
        {page.sections.map((section) => (
          <section className="content-section" id={section.id} key={section.id}>
            {section.eyebrow ? <p className="section-eyebrow">{section.eyebrow}</p> : null}
            {section.title ? <h2>{section.title}</h2> : null}
            {section.summary ? <p className="section-summary">{section.summary}</p> : null}
            <ContentBlocks blocks={section.blocks} />
          </section>
        ))}
      </div>
    </article>
  );
}
