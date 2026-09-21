/*
 * What the server offers, as functions.
 *
 * The reader runs against `serve.js`, which collects a producer's claims for a
 * repository source and has the verifier check them. Every call here is a read:
 * the reader asks for a report and displays it. It never decides an outcome —
 * an outcome in a bundle was reached by the verifier, and a bundle that carries
 * none says so rather than being filled in.
 */
import type { Bundle, Candidate, ExampleGroup, Producer } from "../../types.ts";

/* What the picker lists, declared where the reader's other documents are so
 * the server and the page cannot drift apart over it. */
export type { ExampleGroup as Group } from "../../types.ts";

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
  return get<{ files: string[]; groups: ExampleGroup[] }>("/api/files");
}

/** Repository sources matching a query, for the path field's suggestions. */
export function sources(query: string) {
  return get<{ files: string[]; total: number }>("/api/sources", { q: query });
}

/**
 * Check an edited candidate against unchanged source. The producer is not run:
 * this is the reader's own draft, and what comes back is a report of what the
 * verifier made of it — an unchecked candidate is never displayed as a result.
 */
export async function checkCandidate(candidate: Candidate) {
  const response = await fetch("/api/candidate", {
    method: "POST",
    headers: { "content-type": "application/json" },
    body: JSON.stringify({ candidate }),
  });
  const body = await response.json().catch(() => null);
  if (!response.ok)
    throw new ApiError(
      response.status,
      (body as { error?: string })?.error ?? "the candidate was not accepted",
    );
  return body as Bundle;
}

/**
 * Keep the draft beside the source it is about, or discard it. This writes into
 * the working tree, so it happens only when asked; what is written is the
 * candidate itself, so the same file can be handed to `annotate-source.mts`.
 */
export async function keepDraft(candidate: Candidate, remove = false) {
  const response = await fetch("/api/draft", {
    method: "POST",
    headers: { "content-type": "application/json" },
    body: JSON.stringify({ candidate, file: candidate.file, remove }),
  });
  const body = await response.json().catch(() => null);
  if (!response.ok)
    throw new ApiError(
      response.status,
      (body as { error?: string })?.error ?? "the draft was not kept",
    );
  return body as { path: string; kept: boolean };
}

/**
 * Collect one file's claims from one producer and check them. This runs the
 * producer and the verifier, so it is the expensive call; the server allows one
 * at a time and answers 409 while another is running.
 */
export function analyse(path: string, producer: Producer) {
  return get<Bundle>("/api/analyse", { path, producer });
}
