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
  keepDraft,
  type Group,
} from "./api.ts";
import {
  addClaim,
  addFunction,
  editClaim,
  type ClaimSite,
} from "../../candidate.mts";
import { fromBundle, type Report, type ShownFunction } from "../../model.mts";
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
  /** Index into the function's sites, in source order. */
  site: number | null;
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
  /** Where the kept draft sits, once one has been written beside the source. */
  draftPath = $state("");
  /**
   * The draft kept beside the source, not applied. Opening a file shows what
   * the producer said, because that is the finding; a repair is the answer to
   * it and is one step away, not the thing you land on.
   */
  kept = $state<Candidate | null>(null);
  /** True while the kept draft is what is on screen. */
  showingKept = $state(false);
  /** Why a draft beside the source was not used, where one was not. */
  staleDraft = $state("");

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
      this.path = path;
      this.producer = producer;
      this.bundle = bundle;
      this.report = fromBundle(bundle);
      this.collection = bundle.collection ?? null;
      this.candidate = bundle.candidate ?? null;
      this.original = bundle.candidate ?? null;
      this.edited = false;
      this.draftPath = "";
      this.staleDraft = bundle.stale ?? "";
      this.kept = bundle.draft ?? null;
      this.showingKept = false;
      // A fresh report makes the previous selection meaningless: ids identify
      // records within one snapshot, not the same claim across collections.
      this.selection = this.report.functions.length
        ? { functionId: this.report.functions[0].id, site: null }
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
   * Show the draft kept beside the source. It is checked before any of it is
   * displayed — a kept draft is a record of an edit, never a result.
   */
  async showKept() {
    const draft = this.kept;
    if (!draft || this.busy) return;
    // Showing a kept draft edits nothing, so it is not offered to be kept.
    await this.change(() => draft, false);
    if (!this.error) {
      this.showingKept = true;
      this.draftPath = this.path.replace(/\.tsx?$/, "") + ".candidate.json";
    }
  }

  /**
   * Replace one claim and have the verifier check the result. The producer is
   * not run again: the source is unchanged, and what is being checked is the
   * draft. A check that succeeds establishes that function's modeled
   * obligations; it does not make the producer's original claims true.
   */
  async apply(fn: ShownFunction, site: ClaimSite, value: unknown) {
    await this.change((c) => editClaim(c, fn, site, value));
  }

  /**
   * Change the candidate and have the verifier check the result. The producer
   * is not run again: the source is unchanged, and what is being checked is the
   * draft. A check that succeeds establishes that function's modeled
   * obligations; it does not make the producer's original claims true.
   */
  private async change(
    edit: (candidate: Candidate) => Candidate,
    /** False where nothing was edited — a kept draft being shown, say. */
    edited = true,
  ) {
    if (!this.candidate || this.busy) return;
    this.busy = true;
    this.error = "";
    try {
      // `$state` proxies what it holds, and a proxy is not structured-clonable,
      // which is what these edits do to copy the candidate. The snapshot is the
      // plain object the proxy stands for.
      const next = edit($state.snapshot(this.candidate));
      const bundle = await checkCandidate(next);
      this.candidate = next;
      this.edited = edited;
      this.adopt(bundle);
    } catch (e) {
      // A refused candidate stays available for correction, and what was last
      // displayed keeps saying what it said: nothing unchecked is shown as a
      // result.
      this.error = (e as Error).message;
    } finally {
      this.busy = false;
    }
  }

  /** Add a claim where the producer left a site empty, and check the result. */
  async add(fn: ShownFunction, site: ClaimSite, value: unknown) {
    await this.change((c) => addClaim(c, fn, site, value));
  }

  /** Supply the contract for a function the candidate says nothing about. */
  async addContract(
    fn: ShownFunction,
    contract: { params: { name: string; type: unknown }[]; result: unknown },
  ) {
    await this.change((c) => addFunction(c, fn, contract));
  }

  /**
   * Keep the current draft beside the source, or discard the kept one. Applying
   * an edit writes nothing; this is the step that touches the working tree.
   */
  async keep(remove = false) {
    const candidate = remove ? this.original : this.candidate;
    if (!candidate || this.busy) return;
    this.busy = true;
    this.error = "";
    try {
      const kept = await keepDraft($state.snapshot(candidate), remove);
      this.draftPath = kept.kept ? kept.path : "";
    } catch (e) {
      this.error = (e as Error).message;
    } finally {
      this.busy = false;
    }
  }

  /**
   * Put the producer's own claims back on screen, and check them again. A
   * draft beside the source is left alone: it may be a repair that belongs to
   * the file rather than work in progress, and losing one to a stray click
   * would be worse than having to ask for it again.
   */
  async restore() {
    if (!this.original || this.busy) return;
    this.busy = true;
    this.error = "";
    try {
      const bundle = await checkCandidate($state.snapshot(this.original));
      this.candidate = this.original;
      this.edited = false;
      this.showingKept = false;
      this.adopt(bundle);
    } catch (e) {
      this.error = (e as Error).message;
    } finally {
      this.busy = false;
    }
  }

  /** Remove the draft beside the source. Deleting a file is always explicit. */
  async discard() {
    if (!this.draftPath || this.busy) return;
    await this.keep(true);
    if (!this.error) await this.restore();
  }

  /**
   * Take a rechecked report, keeping the reader looking at the same function.
   * Ids are local to one snapshot — supplying a contract turns a function the
   * candidate did not mention into one it does, and its id changes with it — so
   * the selection is re-resolved by name rather than carried across, and the
   * mark is dropped, because a mark index means nothing in a different report.
   */
  private adopt(bundle: Bundle) {
    const was = this.selected?.name;
    this.bundle = bundle;
    this.report = fromBundle(bundle);
    this.collection = bundle.collection ?? null;
    const fn =
      this.functions.find((f) => f.name === was) ?? this.functions[0] ?? null;
    this.selection = fn ? { functionId: fn.id, site: null } : null;
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
