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
} from "../../candidate.js";
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
  /** Where the kept draft sits, once one has been written beside the source. */
  draftPath = $state("");

  /** Only claims whose type the producer could not state. */
  showUnsupported = $state(false);
  /** The producer's own diagnostics, under the spans they name. */
  showProducerErrors = $state(false);

  /** Every mark of the selected function, in the order the source draws them. */
  get marks(): string[] {
    const fn = this.selected;
    if (!fn) return [];
    const ids: string[] = [];
    fn.entries.forEach((_, i) => ids.push("n" + i));
    fn.exprs.forEach((_, i) => ids.push("e" + i));
    fn.gaps.forEach((_, i) => ids.push("g" + i));
    (fn.missingSites ?? []).forEach((_, i) => ids.push("m" + i));
    const at = (id: string) => {
      const list =
        id[0] === "n"
          ? fn.entries
          : id[0] === "e"
            ? fn.exprs
            : id[0] === "g"
              ? fn.gaps
              : (fn.missingSites ?? []);
      return (
        (list[Number(id.slice(1))] as { pos?: [number, number] })?.pos?.[0] ?? 0
      );
    };
    return ids.sort((a, b) => at(a) - at(b));
  }

  /** Step to the next or previous mark of this function, in source order. */
  step(by: 1 | -1) {
    const ids = this.marks;
    if (!ids.length || !this.selection) return;
    const at = ids.indexOf(this.selection.markId ?? "");
    const next = at < 0 ? (by > 0 ? 0 : ids.length - 1) : at + by;
    if (next < 0 || next >= ids.length) return;
    this.selection = { ...this.selection, markId: ids[next]! };
  }

  /** Step to the next or previous function of the file. */
  stepFunction(by: 1 | -1) {
    const fns = this.functions;
    const at = fns.findIndex((f) => f.id === this.selection?.functionId);
    const next = at + by;
    if (next < 0 || next >= fns.length) return;
    this.select(fns[next]!.id);
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
    // A draft beside the source resumes where it was left. It is checked before
    // any of it is displayed — a kept draft is a record of an edit, never a
    // result — and this happens after the collection releases the reader,
    // because checking is itself a change and takes the same guard.
    const draft = this.bundle?.draft;
    if (draft) {
      const at = this.path.replace(/\.tsx?$/, "") + ".candidate.json";
      await this.change(() => draft);
      this.draftPath = at;
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
  private async change(edit: (candidate: Candidate) => Candidate) {
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
      this.edited = true;
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

  /** Put the producer's own claims back, and check them again. */
  async restore() {
    if (!this.original || this.busy) return;
    this.busy = true;
    this.error = "";
    try {
      const bundle = await checkCandidate($state.snapshot(this.original));
      this.candidate = this.original;
      this.edited = false;
      this.adopt(bundle);
    } catch (e) {
      this.error = (e as Error).message;
    } finally {
      this.busy = false;
    }
    // The producer's claims are back, so a kept draft is no longer what is on
    // screen, and leaving it would resume it on the next open. Discarding it
    // waits for the check to release the reader, since it takes the same guard.
    if (!this.error && this.draftPath) await this.keep(true);
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
    this.selection = fn ? { functionId: fn.id, markId: null } : null;
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
