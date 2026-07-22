import { useEffect, useState } from "react";

export type ResourceState<T> =
  | { state: "loading" }
  | { state: "ready"; data: T }
  | { state: "error"; error: Error };

export function useApiResource<T>(
  load: (signal: AbortSignal) => Promise<T>,
  dependencies: readonly unknown[],
): ResourceState<T> {
  const [resource, setResource] = useState<ResourceState<T>>({ state: "loading" });

  useEffect(() => {
    const controller = new AbortController();
    setResource({ state: "loading" });
    load(controller.signal).then(
      (data) => setResource({ state: "ready", data }),
      (error: unknown) => {
        if (!controller.signal.aborted) {
          setResource({
            state: "error",
            error: error instanceof Error ? error : new Error("The request failed."),
          });
        }
      },
    );
    return () => controller.abort();
    // Callers provide the values that identify a request. The load closure itself
    // intentionally stays outside the dependency array.
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, dependencies);

  return resource;
}
