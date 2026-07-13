export function LoadingState({ label = "Loading framework…" }: { label?: string }) {
  return (
    <div className="load-state" role="status">
      <span className="load-state__spinner" aria-hidden="true" />
      {label}
    </div>
  );
}

export function ErrorState({ message }: { message: string }) {
  return (
    <div className="error-state" role="alert">
      <span>Unable to load the framework explorer.</span>
      <code>{message}</code>
    </div>
  );
}
