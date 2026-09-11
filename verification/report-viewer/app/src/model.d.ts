/*
 * The display model and the source-mark logic, as this application uses them.
 *
 * `model.js`, `marks.js` and `obligation.js` are the tested pure logic the old
 * reader was built on: what a bundle means, what the source view draws, and how
 * a verifier diagnostic reads. They are not being rewritten — only the view is
 * — so this declares the part of their surface the application touches. The
 * compiler then holds the boundary: reaching for something undeclared is an
 * error rather than a silent `any`.
 */
declare module "*/model.js" {
  import type { Bundle, Producer, Span } from "../../types.ts";

  /** A claim as the reader shows it, after the model has decoded its type. */
  export interface ShownClaim {
    pos: Span;
    /** Surface syntax, printed from the producer's encoding. */
    type: string;
    /** The producer's own encoding, or null where there was none. */
    encoding: unknown;
    /** That encoding as formatted JSON, for the inspector. */
    raw: string | null;
    recovery?: boolean;
    unavailable?: boolean;
    failure?: string;
    failureKind?: string;
    failureRole?: string;
  }

  export interface ShownBinding {
    name: string;
    type: string;
    encoding?: unknown;
    raw?: string | null;
  }

  export interface ShownEntry {
    pos: Span;
    bindings: ShownBinding[];
    /** Names whose type differs from the preceding entry's. */
    changed: Set<string>;
    recovery?: boolean;
    unsupported?: string[];
    failure?: string;
    failureKind?: string;
  }

  export interface ShownGap {
    pos: Span;
    detail: string;
    reason: string;
    failure?: string;
    failureKind?: string;
  }

  /** One function of the report, with everything the view draws for it. */
  export interface ShownFunction {
    id: string;
    name: string;
    namePos: Span;
    pos: Span;
    signature?: { params: { name: string; type: string }[]; retType: string };
    entries: ShownEntry[];
    exprs: ShownClaim[];
    gaps: ShownGap[];
    /** Sites a located failure names where nothing is claimed. */
    failureSites?: ShownClaim[];
    missingSites?: { kind: "expression" | "environment"; pos: Span }[];
    /** True for a source function the candidate says nothing about at all. */
    candidateMissing?: boolean;
    /** Its parameter names, in source order, for the contract it needs. */
    parameters?: string[];
    /** What the report says about it, where there is no result to report. */
    detail?: string;
    /** The verifier's verdict over this function's claims. */
    status: string;
    /** The producer's own collection outcome. */
    collection?: { completion: string; quality: string; mode: string };
    quality?: string;
    failure?: string;
    obligation?: unknown;
  }

  export interface Report {
    source: string;
    producer: Producer | string;
    functions: ShownFunction[];
    diagnostics?: string;
    missingFunctions?: { name: string; namePos: Span }[];
  }

  export function fromBundle(bundle: Bundle): Report;
  export function summarize(functions: ShownFunction[]): {
    functions: number;
    gaps: number;
    status: Record<string, number>;
  };
  export function signatureText(f: ShownFunction): string;
  export function renderType(raw: string): { text: string };
  export function findMark(
    functions: ShownFunction[],
    id: string,
  ): { fn: ShownFunction; id: string | null; manifestId: string } | null;
  export function markIdOf(
    functions: ShownFunction[],
    index: number,
    id: string,
  ): string;
}

declare module "*/marks.js" {
  import type { ShownFunction, Report } from "*/model.js";

  /** One drawn mark: where it sits, what it says, and how it reads. */
  export interface MarkItem {
    kind: string;
    line: number;
    /** Start column of the span the mark is about, in the monospace grid. */
    col: number;
    /** End column of that span; the bracket is drawn between the two. */
    end: number;
    label: string;
    /** A proof symbol where this claim is the located failure. */
    mark: string;
    /** The obligation's role, where the record names one. */
    tag: string;
    id: string;
    cls: string;
  }

  /** Marks packed onto as few rows as fit, so nesting is visible at a glance. */
  export interface MarkRow {
    items: MarkItem[];
    free: number;
  }

  export interface SourceMarks {
    entries: MarkItem[];
    items: MarkItem[];
  }

  export function sourceMarks(
    report: Report,
    f: ShownFunction,
    options?: {
      density?: "key" | "all";
      unsupported?: boolean;
      producerErrors?: boolean;
    },
  ): SourceMarks;

  /** The two-part outcome: the producer's, then what proof search found. */
  export function outcome(
    f: ShownFunction,
    collection: unknown,
  ): {
    producer: [string, string];
    proof: [string, string];
    disagrees: boolean;
    stamp: string;
  };

  export function firstFailure(
    f: ShownFunction,
  ): { id: string; item: unknown; kind: string } | null;
  export function proofSymbol(failureKind: string): string;
  export function proofLabel(status: string): string;
  export function shortType(type: string): string;
  export function packRows(items: MarkItem[]): MarkRow[];
  export function groupLines(items: MarkItem[]): Map<number, MarkItem[]>;
  export function bracket(width: number): string;
  export function lineStarts(source: string): number[];
  export function lineAt(starts: number[], pos: number): number;
}

declare module "*/obligation.js" {
  import type { Span } from "../../types.ts";

  /** One binding of the context: what was carried, and what was required. */
  export interface ContextRow {
    slot: number;
    binding: string;
    have: string;
    need: string;
    differs: boolean;
  }

  /**
   * A heap fact the obligation needed, where it needed any: the binding it is
   * about, and what is true of it, already phrased ("holds true", "is a read
   * of cell").
   */
  export interface KnowledgeRow {
    slot: number;
    binding: string;
    what: string;
  }

  /** One end of an edge, and where in the source that end sits. */
  export interface Endpoint {
    end: "from" | "to";
    label: number;
    sourceMap: {
      pos: Span | null;
      role: string;
      environmentStart?: number;
      context?: { name: string; span: Span | null }[];
    } | null;
  }

  /**
   * What the verifier had and what had to follow from it. Explanatory metadata
   * about an unsuccessful attempt — never evidence, and never a statement that
   * a claim is false.
   */
  export interface ObligationView {
    kind: string;
    kindLabel: string;
    /** The role's own name, where the record gives a specific one. */
    title: string;
    /** What that role means, in prose. */
    what: string;
    role: string;
    id: string;
    fuel: number;
    phase: string;
    pos: Span | null;
    rows: ContextRow[];
    /** The judgement required, for a node obligation. */
    conclusion: string;
    term?: string;
    endpoints: Endpoint[];
    knowledge: KnowledgeRow[];
    knowledgeIsTheDifference?: boolean;
    observation?: string;
    note?: string;
  }

  const reader: {
    obligationView(obligation: unknown, source?: string): ObligationView | null;
    /**
     * A type, printed from a document's own graph table: labels index `types`,
     * and a clause the reader does not know is shown as its encoding rather
     * than guessed at.
     */
    typeText(types: unknown[], labels: number[], depth?: number): string;
  };
  export default reader;
}

declare module "*/candidate.js" {
  import type { Candidate } from "../../types.ts";
  import type { ShownFunction } from "*/model.js";

  /** Where a claim sits, in the terms the candidate is addressed by. */
  export interface ClaimSite {
    kind: "expression" | "environment";
    pos: [number, number];
  }

  /** The candidate's own value at a site, in the producer's encoding. */
  export function claimValue(
    candidate: Candidate,
    fn: ShownFunction,
    item: ClaimSite,
  ): unknown;

  /**
   * A candidate with one claim replaced. Immutable: editing never changes a
   * source snapshot and never establishes a verification result.
   */
  export function editClaim(
    candidate: Candidate,
    fn: ShownFunction,
    item: ClaimSite,
    value: unknown,
  ): Candidate;

  /**
   * A candidate with a claim added at a site the producer left empty. The site
   * must be one the parse identified for this snapshot: the reader offers
   * attachment points, it does not invent them.
   */
  export function addClaim(
    candidate: Candidate,
    fn: ShownFunction,
    site: ClaimSite,
    value: unknown,
  ): Candidate;

  /**
   * A candidate with a contract for a function it said nothing about. Parameter
   * names and order come from the source; only the types are supplied here.
   */
  export function addFunction(
    candidate: Candidate,
    fn: ShownFunction,
    contract: { params: { name: string; type: unknown }[]; result: unknown },
  ): Candidate;
}

declare module "*/claim-types.js" {
  /** Surface syntax for claim types: printing, and reading back. */
  const surface: {
    /**
     * The claim in surface syntax, or null where this encoding cannot be
     * printed exactly — in which case it is edited as the producer's JSON.
     */
    printClaimValue(kind: string, value: unknown): string | null;
    /**
     * Read surface text back into an encoding, against the claim it came from:
     * what the text names is replaced, and what it cannot name — index
     * signatures, call and construct shapes — is the original's, never
     * invented here.
     */
    readClaimValue(kind: string, text: string, current: unknown): unknown;
  };
  export default surface;
}
