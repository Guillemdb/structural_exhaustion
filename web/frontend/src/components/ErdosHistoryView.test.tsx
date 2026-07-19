import { fireEvent, render, screen } from "@testing-library/react";
import { describe, expect, it, vi } from "vitest";

import { ErdosHistoryView, type ErdosHistorySnapshot } from "./ErdosHistoryView";

const snapshots: ErdosHistorySnapshot[] = [{
  snapshotId: "artifact-a1",
  label: "Rank split connected",
  capturedAt: "2026-07-18T09:30:00Z",
  artifactHash: "a1b2c3d4",
  metrics: [
    { metricId: "bindings", label: "Explicit framework bindings", value: 29 },
    {
      metricId: "registered-transitions",
      label: "Registered transitions reused",
      value: 5,
    },
  ],
  changes: ["Connected the CT15 residual split to the proof map."],
}];

describe("ErdosHistoryView", () => {
  it("labels snapshots as engineering telemetry rather than proof status", () => {
    render(<ErdosHistoryView snapshots={snapshots} activeSnapshotId="artifact-a1" />);

    expect(screen.getByText("Engineering telemetry")).toBeVisible();
    expect(screen.getByLabelText("Telemetry scope")).toHaveTextContent(
      /do not infer, promote, or replace proof status/i,
    );
    expect(screen.getByText("29")).toBeVisible();
    expect(screen.getByText("Connected the CT15 residual split to the proof map.")).toBeVisible();
    expect(screen.getByText("a1b2c3d4")).toBeVisible();
  });

  it("reports the selected recorded snapshot without changing any status", () => {
    const onSnapshotSelect = vi.fn();
    render(<ErdosHistoryView snapshots={snapshots} onSnapshotSelect={onSnapshotSelect} />);

    fireEvent.click(screen.getByRole("button", { name: "Inspect snapshot" }));
    expect(onSnapshotSelect).toHaveBeenCalledWith("artifact-a1");
  });
});
