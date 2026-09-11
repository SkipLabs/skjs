/*
 * What the reader is looking at.
 *
 * One object, because the views are all views of the same thing: a file, read
 * through one producer, with one claim selected. Nothing here decides an
 * outcome — a report carries the verifier's verdicts and this only holds them.
 */
import { analyse, files as fetchFiles, health, type Group } from "./api.ts";
import { fromBundle, type Report, type ShownFunction } from "../../model.js";
import type { Bundle, CollectionRun, Producer } from "../../types.ts";

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
      // A fresh report makes the previous selection meaningless: ids identify
      // records within one snapshot, not the same claim across collections.
      this.selection = this.report.functions.length
        ? { functionId: this.report.functions[0]!.id, markId: null }
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

  select(functionId: string, markId: string | null = null) {
    this.selection = { functionId, markId };
  }
}

export const reader = new Reader();
