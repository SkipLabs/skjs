/*
 * What the reader is looking at.
 *
 * One object, because the views are all views of the same thing: a file, read
 * through one producer, with one claim selected. Nothing here decides an
 * outcome — a report carries the verifier's verdicts and this only holds them.
 */
import { analyse, files as fetchFiles, health, type Group } from "./api.ts";
import { fromBundle, type Report, type ShownFunction } from "../../model.mts";
import type { Bundle, CollectionRun, Producer } from "../../types.ts";

/** Which claim is selected: a function, and a mark within it. */
export interface Selection {
  functionId: string;
  /** A mark id local to the function's own lists (`e3`, `n1`, `g0`), or null. */
  /** Index into the function's sites, in source order. */
  site: number | null;
}

export class Reader {
  /** The repository-relative source being read. */
  path = $state("");
  producer = $state<Producer>("ocaml");
  /** True while the catalogue is up instead of a report. Opening the reader
   * without a file in the link starts here: what can be read is the first
   * thing to find out, and a file chosen for you answers a question nobody
   * asked. */
  browsing = $state(false);
  bundle = $state<Bundle | null>(null);
  report = $state<Report | null>(null);
  collection = $state<CollectionRun | null>(null);
  selection = $state<Selection | null>(null);

  groups = $state<Group[]>([]);
  hasVerifier = $state(false);

  /** True while a collection is running: it runs the producer and the verifier. */
  busy = $state(false);
  error = $state("");

  /** Only claims whose type the producer could not state. */
  showUnsupported = $state(false);
  /** The producer's own diagnostics, under the spans they name. */
  showProducerErrors = $state(false);

  /** Step to the next or previous site of this function, in source order. */
  step(by: 1 | -1) {
    const fn = this.selected;
    if (!fn || !this.selection || !fn.sites.length) return;
    const at = this.selection.site;
    const next = at === null ? (by > 0 ? 0 : fn.sites.length - 1) : at + by;
    if (next < 0 || next >= fn.sites.length) return;
    this.selection = { ...this.selection, site: next };
  }

  /** Step to the next or previous function of the file. */
  stepFunction(by: 1 | -1) {
    const fns = this.functions;
    const at = fns.findIndex((f) => f.id === this.selection?.functionId);
    const next = at + by;
    if (next < 0 || next >= fns.length) return;
    this.select(fns[next].id);
  }

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
      this.browsing = false;
      this.path = path;
      this.producer = producer;
      this.bundle = bundle;
      this.report = fromBundle(bundle);
      this.collection = bundle.collection ?? null;
      // A fresh report makes the previous selection meaningless: ids identify
      // records within one snapshot, not the same claim across collections.
      this.selection = this.report.functions.length
        ? { functionId: this.report.functions[0].id, site: null }
        : null;
    } catch (e) {
      this.error = (e as Error).message;
      this.report = null;
      this.collection = null;
      this.selection = null;
    } finally {
      this.busy = false;
    }
  }

  select(functionId: string, site: number | null = null) {
    this.selection = { functionId, site };
  }

  /**
   * Select whatever claim sits at a source offset, for following a failure to
   * one end of its edge. Nothing is selected where nothing is claimed there:
   * the reader points at a record, it does not invent one.
   */
  selectAt(fn: ShownFunction, offset: number) {
    let best = -1;
    fn.sites.forEach((s, i) => {
      if (!(s.pos[0] <= offset && offset < s.pos[1])) return;
      // The innermost site containing the offset is the one meant.
      if (
        best < 0 ||
        s.pos[1] - s.pos[0] < fn.sites[best].pos[1] - fn.sites[best].pos[0]
      )
        best = i;
    });
    this.select(fn.id, best >= 0 ? best : null);
  }
}

export const reader = new Reader();
