import { Link, NavLink } from "react-router-dom";

import type { ArtifactWarning, VerificationDisplay } from "../types";
import { ERDOS_GYARFAS_PATH } from "../routes";
import { VerificationBadge } from "./VerificationBadge";
import { useDocumentationAudience } from "../audience";

interface AppHeaderProps {
  verification?: VerificationDisplay;
  artifactWarnings?: ArtifactWarning[];
  compact?: boolean;
  showAudienceToggle?: boolean;
}

export function AppHeader({
  verification,
  artifactWarnings = [],
  compact = false,
  showAudienceToggle = false,
}: AppHeaderProps) {
  const { audience, setAudience } = useDocumentationAudience();
  return (
    <>
      <header className={`app-header ${compact ? "app-header--compact" : ""}`}>
        <Link to="/framework/core" className="brand" aria-label="Framework overview">
          <span className="brand__mark" aria-hidden="true">
            SE
          </span>
          <span>
            <span className="brand__name">Structural Exhaustion</span>
            <span className="brand__sub">Framework explorer</span>
          </span>
        </Link>
        <nav className="app-nav" aria-label="Main navigation">
          <NavLink to="/framework/core">Core</NavLink>
          <NavLink to="/framework/tactics">Tactics</NavLink>
          <NavLink to="/framework/graph">Graph</NavLink>
          <NavLink to="/examples">Examples</NavLink>
          <NavLink to={ERDOS_GYARFAS_PATH}>Erdős–Gyárfás</NavLink>
        </nav>
        {showAudienceToggle ? <div className="audience-toggle" role="group" aria-label="Documentation audience">
          <button
            type="button"
            aria-pressed={audience === "mathematician"}
            onClick={() => setAudience("mathematician")}
          >
            Mathematics
          </button>
          <button
            type="button"
            aria-pressed={audience === "leanUser"}
            onClick={() => setAudience("leanUser")}
          >
            Lean user
          </button>
        </div> : null}
        {verification ? <VerificationBadge verification={verification} /> : null}
      </header>
      {artifactWarnings.length ? (
        <aside className="artifact-warning-banner" role="status" aria-label="Stale artifact warning">
          <strong>Generated content may be stale.</strong>
          <span>{artifactWarnings.map((warning) => warning.message).join(" ")}</span>
        </aside>
      ) : null}
    </>
  );
}
