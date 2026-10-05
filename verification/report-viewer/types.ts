import type { ObligationView } from "../tools/diagnostic-view.mts";
import type { ObligationDiagnostic } from "../tools/diagnostic.mts";
import type { Span } from "../tools/span.mts";
import type { RigidParameter } from "../tools/rigid.mts";
/* Declared where it is computed: the report viewer prints the bound, it does not
 * work one out. */
export type { RigidParameter } from "../tools/rigid.mts";
// The report the report viewer displays.
//
// One description of the shape that `tools/annotate-source.js` writes, the
// tests read, and the page renders. It is a display format: nothing here is
// proof evidence, and a field's presence says a tool recorded something, never
// that a claim is true. The wire formats these are derived from are specified
// in ../SOURCE-CLAIMS.md and ../REQUEST-PROTOCOL.md; this file is the report viewer's
// view of them.
//
// Node runs this directly (type stripping, Node 23.6+), so the modules that
// import it need no build. The browser gets the compiled bundle. Keep the
// syntax erasable: no `enum`, no `namespace`, no parameter properties.

/** One source the report viewer offers, with a required one-line description.
 * A name alone answers "which one was it called", which is a question about a
 * file already seen; the description is what makes an unseen one findable. */
export interface GroupFile {
  path: string;
  about: string;
}

/** A named set of sources the picker offers, with a note saying what the set
 * is. */
export interface ExampleGroup {
  label: string;
  note?: string;
  files: GroupFile[];
}

/** How a code unit is named to a report viewer: a function by its name, the module's
 * top-level code, which has none, as its initialization. */
export const unitLabel = (unit: { name: string }): string =>
  unit.name === "" ? "module initialization" : unit.name;

/** What the verifier found for one function, over the producer's claims. */
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
 * Where verification stopped. The report viewer takes the place and the role from
 * this record rather than inferring either from a span: a return contract and
 * the returned expression's own claim share a span and are different
 * obligations.
 */
export type FailureKind =
  /** An expression's own claim did not follow. */
  | "expression-obligation"
  /** A generic value's instance outside its binder's bound, checked outside the graph. */
  | "direct-obligation"
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
  /** The shared control-flow point supplying this claim. */
  point: string;
  /** Stable within one snapshot, not across edits. `f0x3`, `f1e2`, `g0`. */
  id: string;
  pos: Span;
  /** Printed by tools/claim-text.mts. Falls back to the producer's own text. */
  type: string;
  /** The producer's encoding, which the surface text may not name in full. */
  raw?: unknown;
  /** Present when the producer could not decode a type here. */
  unavailable?: boolean;
  /** Set by the report viewer when a failure attaches here. */
  failure?: string;
  failureKind?: FailureKind;
  failureRole?: string;
  /** The rigid parameters this claim names, with the bounds the source
   * declares for them. A claim of `T` states the whole type; the bound is what
   * is known about `T`, and it is written in the source, not in the claim. */
  rigid?: RigidParameter[];
}

export interface Binding {
  name: string;
  type: string;
  raw?: unknown;
  rigid?: RigidParameter[];
}

export interface Entry {
  /** The shared control-flow point supplying this environment. */
  point: string;
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
  /** The syntax kind at that site. */
  syntax?: string;
}

/** The signature a report carries for a function, its types printed. */
export interface Signature {
  params: { name: string; type: string }[];
  retType: string;
  /** The rigid parameters the claimed result names. */
  resultRigid?: RigidParameter[];
}

export interface ReportFunction {
  id: string;
  name: string;
  namePos: Span;
  /** The whole declaration. */
  pos: Span;
  /** The declared result's annotation, where the source has one. */
  resultPos?: Span | null;
  /** Every rigid parameter the source declares for it, in source order. */
  typeParams?: RigidParameter[];
  signature?: Signature;
  entries: Entry[];
  expressions: DisplayClaim[];
  missingSites?: MissingSite[];
  /** TypeScript's own verdict on the function: accepted when none of its
   * diagnostics falls inside it (`typescriptVerdicts`). Display only. */
  typescriptAccepted?: boolean;
}

/**
 * A function the source declares that the producer said nothing about: where
 * the declaration is, and the sites a claim attaches to.
 */
export interface MissingFunction {
  name: string;
  namePos: Span;
  pos: Span;
  missingSites: MissingSite[];
}

/** A span the producer did not visit. */
export interface Gap {
  id: string;
  pos: Span;
  status: string;
}

interface ResultFields {
  /** The function's `id`, not its name: names repeat across files. */
  function: string;
  /**
   * Where checking stopped short of proof search — set when the producer's
   * claims could not be converted, so the outcome is about the input rather
   * than about derivability.
   */
  stage?: "source-extraction";
  /** The verifier's own message, kept verbatim. */
  detail?: string;
  /** Explanatory metadata about an unsuccessful attempt. Never evidence: the
   * writer attaches the record the verifier's own decoder read back, and what
   * the report viewer makes of it changes no outcome. */
  obligation?: ObligationDiagnostic;
  obligationView?: ObligationView;
  /** What a successful check covers, in the verifier's own words. */
  scope?: string;
  /** The certificate that was checked, for provenance only. */
  certificateSha256?: string;
}

/** A failed derivation is unrepresentable without the exact source place at
 * which validation stopped. Other outcomes may carry a location as additional
 * explanation, but only `not-established` requires one. */
export type Result =
  | (ResultFields & { status: "not-established"; location: Failure })
  | (ResultFields & {
      status: Exclude<Status, "not-established">;
      location?: Failure;
    });

export interface Manifest {
  source: { file: string; sha256: string };
  functions: ReportFunction[];
  gaps?: Gap[];
  /** Explicitly `null` when no verifier ran, rather than absent. */
  results?: Result[] | null;
  /** The producer's own stderr for this file, kept verbatim for display. */
  diagnostics?: string;
  missingFunctions?: MissingFunction[];
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
  command: string;
  ranAt: string;
  durationMs: number;
  verified: boolean;
}

/** What a pipeline run decided (`pipeline/verify-source.mts`), as the page shows
 * it: the outcome and the phase that reached it, with the functions a verified
 * run covers or the reason one stopped. It is the pipeline's verdict, never the
 * report viewer's. */
export type PipelineOutcome =
  | { status: "verified"; phase: string; functions: string[] }
  | {
      status: "unsupported" | "unverified" | "exhausted" | "error";
      phase: string;
      detail: string;
    };

/** What the server hands the page. */
export interface Bundle {
  /** The pipeline's outcome, where the report is one pipeline run. */
  outcome?: PipelineOutcome;
  source: string;
  manifest: Manifest;
  annotated?: string;
  collection?: CollectionRun;
}
