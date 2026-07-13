import { Link } from "react-router-dom";

import { routeLabel } from "../graph-data";
import type { RouteRecord } from "../types";

export function RouteList({
  inbound,
  outbound,
}: {
  inbound: RouteRecord[];
  outbound: RouteRecord[];
}) {
  if (!inbound.length && !outbound.length) {
    return <p className="empty-copy">No cross-CT route is currently registered for this tactic.</p>;
  }
  return (
    <div className="route-list">
      {inbound.map((route) => (
        <Link className="route-card" to={`/ct/${route.sourceTacticId}`} key={route.routeId}>
          <span className="route-card__direction">From {route.sourceTacticId}</span>
          <strong>{routeLabel(route)}</strong>
          <span>{route.selectionClass} route</span>
        </Link>
      ))}
      {outbound.map((route) => (
        <Link className="route-card" to={`/ct/${route.targetTacticId}`} key={route.routeId}>
          <span className="route-card__direction">Continue to {route.targetTacticId}</span>
          <strong>{routeLabel(route)}</strong>
          <span>{route.selectionClass} route</span>
        </Link>
      ))}
    </div>
  );
}
