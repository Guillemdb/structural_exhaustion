import { Link } from "react-router-dom";

import { transitionProfileLabel } from "../graph-data";
import type { TransitionProfileRecord } from "../types";

export function TransitionProfileList({
  inbound,
  outbound,
}: {
  inbound: TransitionProfileRecord[];
  outbound: TransitionProfileRecord[];
}) {
  if (!inbound.length && !outbound.length) {
    return (
      <p className="empty-copy">
        No cross-CT transition profile is currently registered for this tactic.
      </p>
    );
  }
  return (
    <div className="transition-profile-list">
      {inbound.map((profile) => (
        <Link
          className="transition-profile-card"
          to={`/ct/${profile.sourceTacticId}`}
          key={profile.profileId}
        >
          <span className="transition-profile-card__direction">
            From {profile.sourceTacticId}
          </span>
          <strong>{transitionProfileLabel(profile)}</strong>
          <span>{profile.selectionClass} profile</span>
        </Link>
      ))}
      {outbound.map((profile) => (
        <Link
          className="transition-profile-card"
          to={`/ct/${profile.targetTacticId}`}
          key={profile.profileId}
        >
          <span className="transition-profile-card__direction">
            Continue to {profile.targetTacticId}
          </span>
          <strong>{transitionProfileLabel(profile)}</strong>
          <span>{profile.selectionClass} profile</span>
        </Link>
      ))}
    </div>
  );
}
