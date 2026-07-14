import { Link, NavLink } from "react-router-dom";

import type { ArtifactWarning, VerificationDisplay } from "../types";
import { ERDOS_GYARFAS_PATH } from "../routes";
import { VerificationBadge } from "./VerificationBadge";

interface AppHeaderProps {
  verification?: VerificationDisplay;
  artifactWarnings?: ArtifactWarning[];
  compact?: boolean;
}

export function AppHeader({
  verification,
  artifactWarnings = [],
  compact = false,
}: AppHeaderProps) {
  return (
    <>
      <header className={`app-header ${compact ? "app-header--compact" : ""}`}>
        <Link to="/framework" className="brand" aria-label="Framework overview">
          <span className="brand__mark" aria-hidden="true">
            SE
          </span>
          <span>
            <span className="brand__name">Structural Exhaustion</span>
            <span className="brand__sub">Framework explorer</span>
          </span>
        </Link>
        <nav className="app-nav" aria-label="Main navigation">
          <NavLink to="/framework">Framework</NavLink>
          <NavLink to="/examples">Examples</NavLink>
          <NavLink to={ERDOS_GYARFAS_PATH}>Erdős–Gyárfás</NavLink>
        </nav>
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
