import { useEffect, useMemo, useState } from "react";

import type { ExampleDeclaration, ExampleSource } from "../types";

type ViewMode = "focus" | "full";

export function LeanSourceViewer({
  sources,
  declarations,
  activeDeclarationId,
  onDeclarationSelect,
}: {
  sources: ExampleSource[];
  declarations: ExampleDeclaration[];
  activeDeclarationId: string | null;
  onDeclarationSelect: (declarationId: string | null) => void;
}) {
  const activeDeclaration = declarations.find(
    (declaration) => declaration.declarationId === activeDeclarationId,
  );
  const [sourceId, setSourceId] = useState(
    activeDeclaration?.sourceId ?? sources[0]?.sourceId ?? "",
  );
  const [mode, setMode] = useState<ViewMode>(activeDeclaration ? "focus" : "full");

  useEffect(() => {
    if (activeDeclaration) {
      setSourceId(activeDeclaration.sourceId);
      setMode("focus");
    }
  }, [activeDeclaration]);

  const source = sources.find((candidate) => candidate.sourceId === sourceId) ?? sources[0];
  const visibleLines = useMemo(() => {
    if (!source) return [];
    const lines = source.content.split("\n");
    const first = mode === "focus" && activeDeclaration
      ? Math.max(1, activeDeclaration.startLine - 4)
      : 1;
    const last = mode === "focus" && activeDeclaration
      ? Math.min(lines.length, activeDeclaration.endLine + 4)
      : lines.length;
    return lines.slice(first - 1, last).map((content, index) => ({
      number: first + index,
      content,
      highlighted: Boolean(
        activeDeclaration &&
        first + index >= activeDeclaration.startLine &&
        first + index <= activeDeclaration.endLine,
      ),
    }));
  }, [activeDeclaration, mode, source]);

  if (!source) {
    return (
      <section className="source-viewer source-viewer--empty">
        <p>No generated source is available for this example.</p>
      </section>
    );
  }

  return (
    <section className="source-viewer" aria-label="Lean source viewer">
      <div className="source-viewer__heading">
        <div>
          <span className="eyebrow">Lean source</span>
          <strong>{source.moduleName}</strong>
          <small>{source.path}</small>
        </div>
        <div className="source-mode" aria-label="Source view mode">
          <button
            type="button"
            className={mode === "focus" ? "is-active" : ""}
            disabled={!activeDeclaration}
            onClick={() => setMode("focus")}
          >
            Focus
          </button>
          <button
            type="button"
            className={mode === "full" ? "is-active" : ""}
            onClick={() => setMode("full")}
          >
            Full file
          </button>
        </div>
      </div>
      <div className="source-selectors">
        <label>
          <span>Module</span>
          <select
            value={source.sourceId}
            onChange={(event) => {
              setSourceId(event.target.value);
              onDeclarationSelect(null);
              setMode("full");
            }}
          >
            {sources.map((candidate) => (
              <option value={candidate.sourceId} key={candidate.sourceId}>
                {candidate.moduleName}
              </option>
            ))}
          </select>
        </label>
        <label>
          <span>Declaration</span>
          <select
            value={activeDeclarationId ?? ""}
            onChange={(event) => onDeclarationSelect(event.target.value || null)}
          >
            <option value="">Full module</option>
            {declarations.map((declaration) => (
              <option value={declaration.declarationId} key={declaration.declarationId}>
                {declaration.name}
              </option>
            ))}
          </select>
        </label>
      </div>
      <div className="source-code" role="region" aria-label={`${source.moduleName} source`}>
        {visibleLines.map((line) => (
          <div
            className={line.highlighted ? "source-line source-line--highlighted" : "source-line"}
            data-line={line.number}
            key={line.number}
          >
            <span aria-hidden="true">{line.number}</span>
            <code>{line.content || " "}</code>
          </div>
        ))}
      </div>
      <div className="source-viewer__footer">
        <span>SHA-256</span><code>{source.sha256}</code>
      </div>
    </section>
  );
}
