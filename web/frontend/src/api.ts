import type {
  DocumentationResponse,
  ErdosProofHistoryResponse,
  ExampleResponse,
  ExamplesResponse,
  FrameworkResponse,
  TacticResponse,
  TacticInternalsResponse,
} from "./types";

export class ApiError extends Error {
  constructor(
    message: string,
    readonly status: number,
  ) {
    super(message);
  }
}

async function getJson<T>(path: string, signal?: AbortSignal): Promise<T> {
  const response = await fetch(path, {
    headers: { Accept: "application/json" },
    signal,
  });
  if (!response.ok) {
    let message = `${response.status} ${response.statusText}`;
    try {
      const body = (await response.json()) as { detail?: string };
      message = body.detail ?? message;
    } catch {
      // Keep the HTTP status text when the response is not JSON.
    }
    throw new ApiError(message, response.status);
  }
  return (await response.json()) as T;
}

export function fetchFramework(signal?: AbortSignal): Promise<FrameworkResponse> {
  return getJson<FrameworkResponse>("/api/v1/framework", signal);
}

export function fetchDocumentation(signal?: AbortSignal): Promise<DocumentationResponse> {
  return getJson<DocumentationResponse>("/api/v1/documentation", signal);
}

export function fetchTactic(
  tacticId: string,
  signal?: AbortSignal,
): Promise<TacticResponse> {
  return getJson<TacticResponse>(`/api/v1/tactics/${encodeURIComponent(tacticId)}`, signal);
}

export function fetchTacticInternals(
  tacticId: string,
  signal?: AbortSignal,
): Promise<TacticInternalsResponse> {
  return getJson<TacticInternalsResponse>(
    `/api/v1/tactics/${encodeURIComponent(tacticId)}/internals`,
    signal,
  );
}

export function fetchExamples(signal?: AbortSignal): Promise<ExamplesResponse> {
  return getJson<ExamplesResponse>("/api/v1/examples", signal);
}

export function fetchExample(
  exampleId: string,
  signal?: AbortSignal,
): Promise<ExampleResponse> {
  return getJson<ExampleResponse>(
    `/api/v1/examples/${encodeURIComponent(exampleId)}`,
    signal,
  );
}

export function fetchErdosProofHistory(
  signal?: AbortSignal,
): Promise<ErdosProofHistoryResponse> {
  return getJson<ErdosProofHistoryResponse>(
    "/api/v1/examples/erdos-64/history",
    signal,
  );
}
