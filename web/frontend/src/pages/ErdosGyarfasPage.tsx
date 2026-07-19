import { useEffect, useState } from "react";

import { fetchErdosProofHistory, fetchExample } from "../api";
import { ErrorState, LoadingState } from "../components/LoadState";
import { ERDOS_GYARFAS_EXAMPLE_ID } from "../routes";
import type { ErdosProofHistoryResponse, ExampleResponse } from "../types";
import { ErdosLivingProofWorkspace } from "./ErdosLivingProofWorkspace";

/** Dedicated reader for the compiled Erdős--Gyárfás Problem 64 artifact. */
export function ErdosGyarfasPage() {
  const [response, setResponse] = useState<ExampleResponse | null>(null);
  const [error, setError] = useState<string | null>(null);
  const [history, setHistory] = useState<ErdosProofHistoryResponse | null>(null);
  const [historyError, setHistoryError] = useState<string | null>(null);

  useEffect(() => {
    const controller = new AbortController();
    fetchExample(ERDOS_GYARFAS_EXAMPLE_ID, controller.signal)
      .then(setResponse)
      .catch((reason: unknown) => {
        if (!controller.signal.aborted) {
          setError(reason instanceof Error ? reason.message : String(reason));
        }
      });
    fetchErdosProofHistory(controller.signal)
      .then(setHistory)
      .catch((reason: unknown) => {
        if (!controller.signal.aborted) {
          setHistoryError(reason instanceof Error ? reason.message : String(reason));
        }
      });
    return () => controller.abort();
  }, []);

  if (error) {
    return <main className="standalone-state"><ErrorState message={error} /></main>;
  }
  if (!response) {
    return <main className="standalone-state"><LoadingState label="Loading Erdős–Gyárfás formalization…" /></main>;
  }
  return (
    <ErdosLivingProofWorkspace
      response={response}
      history={history}
      historyError={historyError}
    />
  );
}
