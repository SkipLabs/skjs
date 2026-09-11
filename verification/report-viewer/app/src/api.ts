/*
 * What the server offers, as functions.
 *
 * The reader runs against `serve.js`, which collects a producer's claims for a
 * repository source and has the verifier check them. Every call here is a read:
 * the reader asks for a report and displays it. It never decides an outcome —
 * an outcome in a bundle was reached by the verifier, and a bundle that carries
 * none says so rather than being filled in.
 */
import type { Bundle, Producer } from "../../types.ts";

/** A named group of corpus files, as the example picker lists them. */
export interface Group {
  label: string;
  files: string[];
}

export class ApiError extends Error {
  readonly status: number;
  constructor(status: number, message: string) {
    super(message);
    this.status = status;
  }
}

async function get<T>(path: string, params: Record<string, string> = {}) {
  const url = new URL(path, location.origin);
  for (const [k, v] of Object.entries(params)) url.searchParams.set(k, v);
  const response = await fetch(url, {
    headers: { accept: "application/json" },
  });
  const body = await response.json().catch(() => null);
  if (!response.ok)
    throw new ApiError(
      response.status,
      (body as { error?: string })?.error ?? `${path} failed`,
    );
  return body as T;
}

/** Whether a verifier binary is built. Without one, nothing can be checked. */
export function health() {
  return get<{ verifier: boolean }>("/api/health");
}

/** The corpus, as the picker groups it. */
export function files() {
  return get<{ files: string[]; groups: Group[] }>("/api/files");
}

/** Repository sources matching a query, for the path field's suggestions. */
export function sources(query: string) {
  return get<{ files: string[]; total: number }>("/api/sources", { q: query });
}

/**
 * Collect one file's claims from one producer and check them. This runs the
 * producer and the verifier, so it is the expensive call; the server allows one
 * at a time and answers 409 while another is running.
 */
export function analyse(path: string, producer: Producer) {
  return get<Bundle>("/api/analyse", { path, producer });
}
