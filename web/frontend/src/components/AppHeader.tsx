import { Link, NavLink } from "react-router-dom";

import type { VerificationDisplay } from "../types";
import { VerificationBadge } from "./VerificationBadge";

interface AppHeaderProps {
  verification?: VerificationDisplay;
  compact?: boolean;
}

export function AppHeader({ verification, compact = false }: AppHeaderProps) {
  return (
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
      </nav>
      {verification ? <VerificationBadge verification={verification} /> : null}
    </header>
  );
}
