import { useEffect, useState } from "react";

import { fetchExample } from "../api";
import { ErrorState, LoadingState } from "../components/LoadState";
import { ERDOS_GYARFAS_EXAMPLE_ID } from "../routes";
import type { ExampleResponse } from "../types";
import { ExampleWorkspace } from "./ExamplePage";

/** Dedicated reader for the compiled Erdős--Gyárfás Problem 64 artifact. */
export function ErdosGyarfasPage() {
  const [response, setResponse] = useState<ExampleResponse | null>(null);
  const [error, setError] = useState<string | null>(null);

  useEffect(() => {
    const controller = new AbortController();
    fetchExample(ERDOS_GYARFAS_EXAMPLE_ID, controller.signal)
      .then(setResponse)
      .catch((reason: unknown) => {
        if (!controller.signal.aborted) {
          setError(reason instanceof Error ? reason.message : String(reason));
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
  return <ExampleWorkspace response={response} mode="erdos" />;
}
