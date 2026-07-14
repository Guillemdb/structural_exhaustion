export const ERDOS_GYARFAS_EXAMPLE_ID = "erdos-64";
export const ERDOS_GYARFAS_PATH = "/erdos-gyarfas";

/** Return the canonical proof-reader route for a compiled example. */
export function exampleDestination(exampleId: string): string {
  return exampleId === ERDOS_GYARFAS_EXAMPLE_ID
    ? ERDOS_GYARFAS_PATH
    : `/examples/${encodeURIComponent(exampleId)}`;
}
