import type { ObligationView } from "../tools/diagnostic-view.mts";
import type { Span } from "../tools/span.mts";
// The report the reader displays.
//
// One description of the shape that `tools/annotate-source.js` writes, the
// tests read, and the page renders. It is a display format: nothing here is
// proof evidence, and a field's presence says a tool recorded something, never
// that a claim is true. The wire formats these are derived from are specified
// in ../SOURCE-CLAIMS.md and ../REQUEST-PROTOCOL.md; this file is the reader's
// view of them.
//
// Node runs this directly (type stripping, Node 23.6+), so the modules that
// import it need no build. The browser gets the compiled bundle. Keep the
// syntax erasable: no `enum`, no `namespace`, no parameter properties.

/** Which checker supplied the claims a report displays. */
export type Producer = "skjs" | "tsc" | "manual" | "edited candidate";

/** What the verifier found for one function, over one producer's claims. */
export type Status =
  /** A certificate was checked. */
  | "verified"
  /** Proof search found no derivation. Never a statement that a claim is false. */
  | "not-established"
  /** Checking could not be attempted: the source or the claim is outside the fragment. */
  | "unsupported"
  /** No verifier ran for this report. */
  | "not-run";

/**
 * Where verification stopped. The reader takes the place and the role from
 * this record rather than inferring either from a span: a return contract and
 * the returned expression's own claim share a span and are different
 * obligations.
 */
export type FailureKind =
  /** An expression's own claim did not follow. */
  | "expression-obligation"
  /** An edge into a statement entry did not justify what the entry claims. */
  | "edge-obligation"
  /** A statement entry's environment did not convert. */
  | "environment-obligation"
  /** A parameter claim contradicts the annotation the caller is held to. */
  | "parameter-claim"
  /** The producer exported no usable type for something extraction needed. */
  | "unavailable-type-claim"
  /** Extraction needed a claim that is absent. */
  | "missing-expression-claim"
  | "missing-environment-claim"
  /** Conversion stopped before checking: this is not a verdict on a claim. */
  | "source-limitation";

export interface Failure {
  kind: FailureKind;
  /** The expression span, where the record names one. */
  pos?: Span;
  /** The statement entry's start, where the record names one instead. */
  start?: number;
  /** The binding a claim or unavailable type concerns. */
  binding?: string;
  /** Why a type was unavailable, as the producer's own slug. */
  reason?: string;
}

/** One claim, as the page shows it: surface syntax, with the encoding beside it. */
export interface DisplayClaim {
  /** Stable within one snapshot, not across edits. `f0x3`, `f1e2`, `g0`. */
  id: string;
  pos: Span;
  /** Printed by tools/claim-text.mts. Falls back to the producer's own text. */
  type: string;
  /** The producer's encoding, which the surface text may not name in full. */
  raw?: unknown;
  /** Present when the producer could not decode a type here. */
  unavailable?: boolean;
  /** Set by the reader when a failure attaches here. */
  failure?: string;
  failureKind?: FailureKind;
  failureRole?: string;
}

export interface Binding {
  name: string;
  type: string;
  raw?: unknown;
}

export interface Entry {
  id: string;
  pos: Span;
  bindings: Binding[];
  /** Names the producer could not decode at this entry. */
  unsupported?: string[];
}

/** A site the lowering visits for which the producer made no claim. */
export interface MissingSite {
  kind: "expression" | "environment";
  pos: Span;
  /** The syntax kind at that site, for a reader choosing what to write. */
  syntax?: string;
}

export interface Signature {
  params: { name: string; type: string }[];
  retType: string;
}

/** How complete the producer's own collection was for this function. */
export interface Collection {
  completion: "complete" | "aborted";
  quality: "unverified" | "recovery";
  mode: "normal" | "keep-going" | "backtrace";
  /**
   * Original spans expression checking entered, including expressions that
   * failed before a result could be recorded (ANNOTATED-SOURCE.md). A gap is
   * one of these with no claim against it.
   */
  visitedExpressions?: Span[];
}

export interface ReportFunction {
  id: string;
  name: string;
  namePos: Span;
  /** The whole declaration. */
  pos: Span;
  /** The declared result's annotation, where the source has one. */
  resultPos?: Span | null;
  signature?: Signature;
  entries: Entry[];
  expressions: DisplayClaim[];
  missingSites?: MissingSite[];
  collection?: Collection;
}

/** A span the producer did not visit, or an edit recorded against a baseline. */
export interface Gap {
  id: string;
  pos: Span;
  status: string;
}

export interface Result {
  /** The function's `id`, not its name: names repeat across files. */
  function: string;
  status: Status;
  /**
   * Where checking stopped short of proof search — set when the producer's
   * claims could not be converted, so the outcome is about the input rather
   * than about derivability.
   */
  stage?: "source-extraction";
  /** The verifier's own message, kept verbatim. */
  detail?: string;
  location?: Failure;
  /** Explanatory metadata about an unsuccessful attempt. Never evidence. */
  obligation?: unknown;
  obligationView?: ObligationView;
  /** What a successful check covers, in the verifier's own words. */
  scope?: string;
  /** The certificate that was checked, for provenance only. */
  certificateSha256?: string;
}

export interface Manifest {
  source: { file: string; sha256: string };
  producer: Producer | string;
  functions: ReportFunction[];
  gaps?: Gap[];
  /** Explicitly `null` when no verifier ran, rather than absent. */
  results?: Result[] | null;
  /** The producer's own stderr for this file, kept verbatim for display. */
  diagnostics?: string;
  missingFunctions?: { name: string; namePos: Span }[];
  /** Fingerprints of what produced this report, for provenance only. */
  claimsSha256?: string;
  verifierSha256?: string;
  annotatedSha256?: string;
  sourcePath?: string;
  claimsPath?: string;
  verifierPath?: string;
}

/** How the report was collected, shown under provenance. */
export interface CollectionRun {
  producer: Producer | string;
  producerRun: boolean;
  command: string;
  ranAt: string;
  durationMs: number;
  verified: boolean;
}

/** An editable copy of the producer's claims, kept beside the original. */
export interface Candidate {
  format: "skjs" | "source-claims";
  file: string;
  sourceSha256: string;
  claims: unknown;
}

/** What the server hands the page. */
export interface Bundle {
  source: string;
  manifest: Manifest;
  annotated?: string;
  collection?: CollectionRun;
  /** The producer's own claims, as an editable copy. */
  candidate?: Candidate;
  /**
   * A draft kept beside the source, where one exists and is about this exact
   * source. It is a record of an edit, never a result: what it claims is
   * checked before anything is displayed.
   */
  draft?: Candidate;
  /**
   * Why a draft beside the source was not used. A file that silently does
   * nothing is worse than one that says what is wrong with it.
   */
  stale?: string;
}
