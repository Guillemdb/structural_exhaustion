import { useEffect, useRef, useState } from "react";

type CopyState = "idle" | "copied" | "failed";

export function CopyButton({ text, label = "code" }: { text: string; label?: string }) {
  const [state, setState] = useState<CopyState>("idle");
  const resetTimer = useRef<number | null>(null);

  useEffect(() => {
    setState("idle");
    return () => {
      if (resetTimer.current !== null) window.clearTimeout(resetTimer.current);
    };
  }, [text]);

  async function copy() {
    try {
      if (!navigator.clipboard?.writeText) throw new Error("Clipboard API unavailable");
      await navigator.clipboard.writeText(text);
      setState("copied");
    } catch {
      setState("failed");
    }
    if (resetTimer.current !== null) window.clearTimeout(resetTimer.current);
    resetTimer.current = window.setTimeout(() => setState("idle"), 2400);
  }

  const visibleLabel = state === "copied"
    ? "Copied"
    : state === "failed" ? "Copy failed" : "Copy";
  const announcement = state === "copied"
    ? `${label} copied to clipboard.`
    : state === "failed" ? `Could not copy ${label} to the clipboard.` : "";

  return (
    <>
      <button
        className={`copy-button copy-button-${state}`}
        type="button"
        aria-label={`Copy ${label}`}
        onClick={() => void copy()}
      >
        {visibleLabel}
      </button>
      <span className="sr-only" role="status" aria-live="polite">
        {announcement}
      </span>
    </>
  );
}
