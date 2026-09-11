/*
 * What the reader is looking at.
 *
 * One object, because the views are all views of the same thing: a file, read
 * through one producer, with one claim selected. Nothing here decides an
 * outcome — a report carries the verifier's verdicts and this only holds them.
 */
import {
  analyse,
  checkCandidate,
  files as fetchFiles,
  health,
  type Group,
} from "./api.ts";
import { editClaim, type ClaimSite } from "../../candidate.js";
import { fromBundle, type Report, type ShownFunction } from "../../model.js";
import type {
  Bundle,
  Candidate,
  CollectionRun,
  Producer,
} from "../../types.ts";

/** Which claim is selected: a function, and a mark within it. */
export interface Selection {
  functionId: string;
  /** A mark id local to the function's own lists (`e3`, `n1`, `g0`), or null. */
  markId: string | null;
}

export class Reader {
  /** The repository-relative source being read. */
  path = $state("");
  producer = $state<Producer>("skjs");
  bundle = $state<Bundle | null>(null);
  report = $state<Report | null>(null);
  collection = $state<CollectionRun | null>(null);
  selection = $state<Selection | null>(null);

  groups = $state<Group[]>([]);
  hasVerifier = $state(false);

  /** True while a collection is running: it runs the producer and the verifier. */
  busy = $state(false);
  error = $state("");

  /** The editable copy of the producer's claims, where the report carries one. */
  candidate = $state<Candidate | null>(null);
  /** The producer's own claims, to restore the candidate to. */
  original = $state<Candidate | null>(null);
  /** True once the candidate differs from what the producer said. */
  edited = $state(false);

  /** Only claims whose type the producer could not state. */
  showUnsupported = $state(false);
  /** The producer's own diagnostics, under the spans they name. */
  showProducerErrors = $state(false);

  get functions(): ShownFunction[] {
    return this.report?.functions ?? [];
  }

  get selected(): ShownFunction | null {
    const id = this.selection?.functionId;
    return this.functions.find((f) => f.id === id) ?? null;
  }

  async start() {
    const [{ verifier }, listing] = await Promise.all([health(), fetchFiles()]);
    this.hasVerifier = verifier;
    this.groups = listing.groups;
  }

  /**
   * Collect and check one file. The producer runs every time — nothing is
   * cached — so this is the expensive path and the one the busy flag guards.
   */
  async open(path: string, producer: Producer = this.producer) {
    if (!path || this.busy) return;
    this.busy = true;
    this.error = "";
    try {
      const bundle = await analyse(path, producer);
      this.path = path;
      this.producer = producer;
      this.bundle = bundle;
      this.report = fromBundle(bundle);
      this.collection = bundle.collection ?? null;
      this.candidate = bundle.candidate ?? null;
      this.original = bundle.candidate ?? null;
      this.edited = false;
      // A fresh report makes the previous selection meaningless: ids identify
      // records within one snapshot, not the same claim across collections.
      this.selection = this.report.functions.length
        ? { functionId: this.report.functions[0]!.id, markId: null }
        : null;
    } catch (e) {
      this.error = (e as Error).message;
      this.report = null;
      this.collection = null;
      this.candidate = null;
      this.original = null;
      this.selection = null;
    } finally {
      this.busy = false;
    }
  }

  /**
   * Replace one claim and have the verifier check the result. The producer is
   * not run again: the source is unchanged, and what is being checked is the
   * draft. A check that succeeds establishes that function's modeled
   * obligations; it does not make the producer's original claims true.
   */
  async apply(fn: ShownFunction, site: ClaimSite, value: unknown) {
    if (!this.candidate || this.busy) return;
    this.busy = true;
    this.error = "";
    try {
      // `$state` proxies what it holds, and a proxy is not structured-clonable,
      // which is what `editClaim` does to copy the candidate. The snapshot is
      // the plain object the proxy stands for.
      const next = editClaim($state.snapshot(this.candidate), fn, site, value);
      const bundle = await checkCandidate(next);
      this.candidate = next;
      this.edited = true;
      this.bundle = bundle;
      this.report = fromBundle(bundle);
      this.collection = bundle.collection ?? null;
    } catch (e) {
      // A refused candidate stays available for correction, and what was last
      // displayed keeps saying what it said: nothing unchecked is shown as a
      // result.
      this.error = (e as Error).message;
    } finally {
      this.busy = false;
    }
  }

  /** Put the producer's own claims back, and check them again. */
  async restore() {
    if (!this.original || this.busy) return;
    this.busy = true;
    this.error = "";
    try {
      const bundle = await checkCandidate($state.snapshot(this.original));
      this.candidate = this.original;
      this.edited = false;
      this.bundle = bundle;
      this.report = fromBundle(bundle);
      this.collection = bundle.collection ?? null;
    } catch (e) {
      this.error = (e as Error).message;
    } finally {
      this.busy = false;
    }
  }

  select(functionId: string, markId: string | null = null) {
    this.selection = { functionId, markId };
  }

  /**
   * Select whatever claim sits at a source offset, for following a failure to
   * one end of its edge. Nothing is selected where nothing is claimed there:
   * the reader points at a record, it does not invent one.
   */
  selectAt(fn: ShownFunction, offset: number) {
    const at = <T extends { pos: [number, number] }>(list: T[]) =>
      list.findIndex((x) => x.pos[0] <= offset && offset < x.pos[1]);
    for (const [prefix, list] of [
      ["e", fn.exprs],
      ["n", fn.entries],
      ["g", fn.gaps],
    ] as const) {
      const i = at(list as { pos: [number, number] }[]);
      if (i >= 0) return this.select(fn.id, prefix + i);
    }
    this.select(fn.id, null);
  }
}

export const reader = new Reader();
