import { useEffect, useMemo, useState } from "react";

import type {
  ExampleDeclaration,
  ExampleManuscript,
  ExampleProofStep,
  ExampleSource,
} from "../types";
import { ManuscriptFragmentViewer } from "./ManuscriptFragmentViewer";

type SourceViewMode = "focus" | "full";
type CompanionMode = "lean" | "paper";

export function LeanSourceViewer({
  sources,
  declarations,
  activeDeclarationId,
  onDeclarationSelect,
  manuscript,
  proofStep,
  paperEnabled = false,
}: {
  sources: ExampleSource[];
  declarations: ExampleDeclaration[];
  activeDeclarationId: string | null;
  onDeclarationSelect: (declarationId: string | null) => void;
  manuscript?: ExampleManuscript | null;
  proofStep?: ExampleProofStep;
  paperEnabled?: boolean;
}) {
  const activeDeclaration = declarations.find(
    (declaration) => declaration.declarationId === activeDeclarationId,
  );
  const [sourceId, setSourceId] = useState(
    activeDeclaration?.sourceId ?? sources[0]?.sourceId ?? "",
  );
  const [sourceMode, setSourceMode] = useState<SourceViewMode>(activeDeclaration ? "focus" : "full");
  const [companionMode, setCompanionMode] = useState<CompanionMode>("lean");

  useEffect(() => {
    if (activeDeclaration) {
      setSourceId(activeDeclaration.sourceId);
      setSourceMode("focus");
    }
  }, [activeDeclaration]);

  useEffect(() => {
    if (!paperEnabled || !manuscript) setCompanionMode("lean");
  }, [manuscript, paperEnabled]);

  const source = sources.find((candidate) => candidate.sourceId === sourceId) ?? sources[0];
  const visibleLines = useMemo(() => {
    if (!source) return [];
    const lines = source.content.split("\n");
    const first = sourceMode === "focus" && activeDeclaration
      ? Math.max(1, activeDeclaration.startLine - 4)
      : 1;
    const last = sourceMode === "focus" && activeDeclaration
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
  }, [activeDeclaration, sourceMode, source]);

  if (!source) {
    return (
      <section className="source-viewer source-viewer--empty">
        <p>No generated source is available for this example.</p>
      </section>
    );
  }

  const showPaper = paperEnabled && manuscript && companionMode === "paper";

  return (
    <section className="source-viewer" aria-label={paperEnabled ? "Lean and manuscript companion" : "Lean source viewer"}>
      <div className="source-viewer__heading">
        <div>
          <span className="eyebrow">{showPaper ? "Rendered paper" : "Lean source"}</span>
          <strong>{showPaper ? manuscript.title : source.moduleName}</strong>
          <small>{showPaper ? manuscript.path : source.path}</small>
        </div>
        {paperEnabled && manuscript ? (
          <div className="source-mode" aria-label="Companion view mode">
            <button
              type="button"
              className={companionMode === "lean" ? "is-active" : ""}
              onClick={() => setCompanionMode("lean")}
            >
              Lean
            </button>
            <button
              type="button"
              className={companionMode === "paper" ? "is-active" : ""}
              onClick={() => setCompanionMode("paper")}
            >
              Paper
            </button>
          </div>
        ) : (
          <SourceModeButtons
            mode={sourceMode}
            disabled={!activeDeclaration}
            onChange={setSourceMode}
          />
        )}
      </div>
      {showPaper ? (
        <ManuscriptFragmentViewer manuscript={manuscript} proofStep={proofStep} />
      ) : (
        <>
          <div className={`source-selectors ${paperEnabled ? "source-selectors--with-mode" : ""}`}>
            <label>
              <span>Module</span>
              <select
                value={source.sourceId}
                onChange={(event) => {
                  setSourceId(event.target.value);
                  onDeclarationSelect(null);
                  setSourceMode("full");
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
            {paperEnabled ? (
              <div className="source-focus-control">
                <span>Source view</span>
                <SourceModeButtons
                  mode={sourceMode}
                  disabled={!activeDeclaration}
                  onChange={setSourceMode}
                />
              </div>
            ) : null}
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
        </>
      )}
      <div className="source-viewer__footer">
        <span>SHA-256</span><code>{showPaper ? manuscript.sha256 : source.sha256}</code>
      </div>
    </section>
  );
}

function SourceModeButtons({
  mode,
  disabled,
  onChange,
}: {
  mode: SourceViewMode;
  disabled: boolean;
  onChange: (mode: SourceViewMode) => void;
}) {
  return (
    <div className="source-mode" aria-label="Source view mode">
      <button
        type="button"
        className={mode === "focus" ? "is-active" : ""}
        disabled={disabled}
        onClick={() => onChange("focus")}
      >
        Focus
      </button>
      <button
        type="button"
        className={mode === "full" ? "is-active" : ""}
        onClick={() => onChange("full")}
      >
        Full file
      </button>
    </div>
  );
}
