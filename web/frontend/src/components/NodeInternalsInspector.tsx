import type {
  InternalDeclaration,
  InternalSource,
  SelectedGraphElement,
  TacticInternalsResponse,
} from "../types";
import { MathFormula } from "./MathFormula";

function SourceExcerpt({
  declaration,
  source,
}: {
  declaration: InternalDeclaration;
  source?: InternalSource;
}) {
  if (!source || !declaration.range) {
    return <p className="empty-copy">No project source range is available.</p>;
  }
  const lines = source.content.split("\n");
  const first = Math.max(0, declaration.range.start.line - 2);
  const last = Math.min(lines.length - 1, declaration.range.end.line + 2);
  const excerpt = lines.slice(first, last + 1);
  return (
    <div className="lean-source-excerpt">
      <div>
        <code>{source.path}:{declaration.range.start.line + 1}</code>
        <span>SHA-256 {source.sha256.slice(0, 12)}…</span>
      </div>
      <pre aria-label={`Lean source for ${declaration.name}`}>
        {excerpt.map((line, index) => {
          const lineNumber = first + index;
          const focused = lineNumber >= declaration.range!.start.line
            && lineNumber <= declaration.range!.end.line;
          return (
            <span className={focused ? "is-focused" : ""} key={lineNumber}>
              <i>{String(lineNumber + 1).padStart(4, " ")}</i>{line}{"\n"}
            </span>
          );
        })}
      </pre>
    </div>
  );
}

function DependencyList({
  title,
  values,
}: {
  title: string;
  values: string[];
}) {
  return (
    <section className="inspector-section">
      <h4>{title}</h4>
      {values.length ? (
        <ul className="internal-dependency-list">
          {values.map((value) => <li key={value}><code>{value}</code></li>)}
        </ul>
      ) : <p className="empty-copy">None</p>}
    </section>
  );
}

export function NodeInternalsInspector({
  nodeId,
  selected,
  response,
  expandedDeclarations,
  onExpandDeclaration,
}: {
  nodeId: string;
  selected: SelectedGraphElement;
  response: TacticInternalsResponse;
  expandedDeclarations: ReadonlySet<string>;
  onExpandDeclaration: (declarationId: string) => void;
}) {
  const internalNode = response.internals.nodes.find((item) => item.nodeId === nodeId);
  const stepId = typeof selected.data.stepId === "string" ? selected.data.stepId : null;
  const step = internalNode?.internalFlow.steps.find((item) => item.stepId === stepId);
  const declarationId = typeof selected.data.declarationId === "string"
    ? selected.data.declarationId
    : step?.declarationId;
  const declaration = response.internals.declarations.find(
    (item) => item.declarationId === declarationId,
  );
  const source = response.internals.sources.find(
    (item) => item.sourceId === declaration?.sourceId,
  );
  const dependencies = declaration
    ? [...new Set([...declaration.typeDependencies, ...declaration.bodyDependencies])]
    : [];

  if (selected.data.internalKind === "declaration" && !declaration) {
    return (
      <aside className="inspector-panel" aria-label="Node internals inspector">
        <div className="inspector-heading">
          <span className="kind-chip kind-chip--internal-declaration">external dependency</span>
          <h2>{declarationId}</h2>
          <p>
            This Lean or Mathlib declaration is an external boundary dependency.
            The low-level view names it exactly but does not recursively expand
            third-party implementation code.
          </p>
        </div>
        <div className="inspector-body">
          <section className="inspector-section">
            <h4>Exact Lean name</h4>
            <code>{declarationId}</code>
          </section>
        </div>
      </aside>
    );
  }

  if (!step && !declaration) {
    return (
      <aside className="inspector-panel" aria-label="Node internals inspector">
        <div className="inspector-heading">
          <span className="kind-chip kind-chip--edge">internal relation</span>
          <h2>{selected.data.label as string ?? selected.id}</h2>
          <p>This edge is part of the Lean-owned flow inside {nodeId}.</p>
        </div>
        <div className="inspector-body">
          <dl className="property-list">
            <div><dt>Source</dt><dd><code>{String(selected.data.source ?? "")}</code></dd></div>
            <div><dt>Target</dt><dd><code>{String(selected.data.target ?? "")}</code></dd></div>
          </dl>
        </div>
      </aside>
    );
  }

  const title = step?.label ?? declaration!.name;
  const plainExplanation = step?.plainExplanation
    ?? declaration?.docString
    ?? `This Lean ${declaration?.kind ?? "declaration"} is a compiled dependency of ${nodeId}.`;
  return (
    <aside className="inspector-panel" aria-label="Node internals inspector">
      <div className="inspector-heading">
        <span className={`kind-chip kind-chip--internal-${step?.role ?? "declaration"}`}>
          {step?.role ?? declaration?.kind}
        </span>
        <h2>{title}</h2>
        <p>{plainExplanation}</p>
      </div>
      <div className="inspector-body">
        {step?.mathematicalDefinition ? (
          <section className="inspector-section">
            <h4>Formal mathematical meaning</h4>
            <MathFormula
              value={step.mathematicalDefinition}
              label={`Formal mathematical meaning of ${step.label}`}
            />
          </section>
        ) : null}
        <section className="inspector-section">
          <h4>Exact Lean interface</h4>
          {declaration ? (
            <>
              <code>{declaration.name}</code>
              <pre>{declaration.type}</pre>
            </>
          ) : (
            <>
              <code>{step?.reference.ref}</code>
              <p className="empty-copy">No compiled declaration resolves this typed state label.</p>
            </>
          )}
          {step ? (
            <span className="provision-badge">
              {step.reference.provision.replaceAll("_", " ")}
            </span>
          ) : null}
        </section>
        {declaration ? (
          <>
            <dl className="property-list">
              <div><dt>Kind</dt><dd>{declaration.kind}</dd></div>
              <div><dt>Module</dt><dd>{declaration.module ?? "External / compiler-owned"}</dd></div>
              <div><dt>Project local</dt><dd>{declaration.projectLocal ? "Yes" : "No"}</dd></div>
              <div><dt>Body available</dt><dd>{declaration.bodyAvailable ? "Yes" : "No"}</dd></div>
            </dl>
            <DependencyList title="Dependencies in the type" values={declaration.typeDependencies} />
            <DependencyList title="Dependencies in the body" values={declaration.bodyDependencies} />
            {declaration.projectLocal && dependencies.length ? (
              <button
                className="internal-expand-button"
                type="button"
                disabled={expandedDeclarations.has(declaration.declarationId)}
                onClick={() => onExpandDeclaration(declaration.declarationId)}
              >
                {expandedDeclarations.has(declaration.declarationId)
                  ? "Direct dependencies shown"
                  : `Show ${dependencies.length} direct dependencies`}
              </button>
            ) : null}
            <section className="inspector-section">
              <h4>Lean source excerpt</h4>
              <SourceExcerpt declaration={declaration} source={source} />
            </section>
          </>
        ) : null}
      </div>
    </aside>
  );
}
