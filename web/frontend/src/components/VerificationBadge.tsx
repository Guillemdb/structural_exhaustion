import type { VerificationDisplay } from "../types";

export function VerificationBadge({ verification }: { verification: VerificationDisplay }) {
  return (
    <span
      className={`verification verification--${verification.state}`}
      title={verification.message}
    >
      <span className="verification__dot" aria-hidden="true" />
      {verification.state === "verified"
        ? "Kernel verified"
        : verification.state === "stale"
          ? "Verification stale"
          : "Verification failed"}
    </span>
  );
}
