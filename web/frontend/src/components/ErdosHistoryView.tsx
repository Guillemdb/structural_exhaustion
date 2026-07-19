export interface ErdosHistoryMetric {
  metricId: string;
  label: string;
  value: string | number;
  detail?: string;
}

export interface ErdosHistorySnapshot {
  snapshotId: string;
  label: string;
  capturedAt: string;
  artifactHash?: string;
  metrics: ErdosHistoryMetric[];
  changes?: string[];
}

export interface ErdosHistoryViewProps {
  snapshots: ErdosHistorySnapshot[];
  activeSnapshotId?: string | null;
  onSnapshotSelect?: (snapshotId: string) => void;
}

/** A chronology of recorded engineering facts; never a proof-status calculator. */
export function ErdosHistoryView({
  snapshots,
  activeSnapshotId = null,
  onSnapshotSelect,
}: ErdosHistoryViewProps) {
  return (
    <section className="erdos-history-view" aria-labelledby="erdos-history-title">
      <header className="erdos-history-view__heading">
        <div>
          <span className="eyebrow">Engineering telemetry</span>
          <h2 id="erdos-history-title">Living implementation history</h2>
        </div>
      </header>
      <aside className="erdos-history-view__disclaimer" aria-label="Telemetry scope">
        These snapshots record implementation activity and framework reuse. They do not infer,
        promote, or replace proof status; proof status comes only from the current kernel-checked artifact.
      </aside>

      {snapshots.length ? (
        <ol className="erdos-history-timeline">
          {snapshots.map((snapshot) => (
            <li
              className={`erdos-history-snapshot${snapshot.snapshotId === activeSnapshotId ? " is-active" : ""}`}
              key={snapshot.snapshotId}
            >
              <article>
                <header>
                  <div>
                    <h3>{snapshot.label}</h3>
                    <time dateTime={snapshot.capturedAt}>{snapshot.capturedAt}</time>
                  </div>
                  {onSnapshotSelect ? (
                    <button type="button" onClick={() => onSnapshotSelect(snapshot.snapshotId)}>
                      Inspect snapshot
                    </button>
                  ) : null}
                </header>
                {snapshot.artifactHash ? (
                  <p className="erdos-history-snapshot__artifact">
                    Artifact <code>{snapshot.artifactHash}</code>
                  </p>
                ) : null}
                <dl className="erdos-history-snapshot__metrics">
                  {snapshot.metrics.map((metric) => (
                    <div key={metric.metricId}>
                      <dt>{metric.label}</dt>
                      <dd>{metric.value}</dd>
                      {metric.detail ? <small>{metric.detail}</small> : null}
                    </div>
                  ))}
                </dl>
                {snapshot.changes?.length ? (
                  <section className="erdos-history-snapshot__changes">
                    <h4>Recorded changes</h4>
                    <ul>
                      {snapshot.changes.map((change) => <li key={change}>{change}</li>)}
                    </ul>
                  </section>
                ) : null}
              </article>
            </li>
          ))}
        </ol>
      ) : (
        <p className="empty-copy">
          No historical snapshots have been recorded. The current artifact remains available in the proof view.
        </p>
      )}
    </section>
  );
}
