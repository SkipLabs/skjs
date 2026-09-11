<script lang="ts">
  /*
   * The selected claim, docked under the source it came from.
   *
   * The old reader put this in a side rail, far from the thing clicked. A claim
   * and its detail belong together, so this sits directly beneath the line it
   * is about and the source keeps the full width.
   *
   * Four kinds of site can be selected: the result the function must
   * establish, an expression claim, an environment, and a place with nothing
   * claimed — which, where the lowering attaches a claim there, is where one
   * can be added.
   */
  import ClaimEditor from "./ClaimEditor.svelte";
  import FunctionContract from "./FunctionContract.svelte";
  import { proofLabel } from "../../marks.mts";
  import { editable, type ClaimSite } from "../../candidate.mts";
  import type { Report, ShownFunction, Site } from "../../model.mts";
  import type { Candidate } from "../../types.ts";

  let {
    report,
    fn,
    site: at,
    candidate,
    busy,
    onapply,
    onadd,
    oncontract,
  }: {
    report: Report;
    fn: ShownFunction;
    /** The selected site's index, in source order. */
    site: number | null;
    candidate: Candidate | null;
    busy: boolean;
    onapply: (site: ClaimSite, value: unknown) => void;
    onadd: (site: ClaimSite, value: unknown) => void;
    oncontract: (contract: {
      params: { name: string; type: unknown }[];
      result: unknown;
    }) => void;
  } = $props();

  const picked = $derived<Site | null>(at === null ? null : (fn.sites[at] ?? null));

  /** Where the selected claim sits, in the terms a candidate is addressed by. */
  const site = $derived.by((): ClaimSite | null => {
    if (!picked || picked.kind === "result") return null;
    if (picked.kind === "unclaimed")
      // A place with nothing claimed names the kind of claim that belongs there,
      // where the lowering says one does.
      return picked.claims ? { kind: picked.claims, pos: picked.pos } : null;
    return { kind: picked.kind, pos: picked.pos };
  });

  /** The candidate's value at the site, as the editor reads and writes it. */
  const current = $derived.by(() => {
    if (!candidate || !site || picked?.kind === "unclaimed") return undefined;
    try {
      return editable(candidate, fn, site);
    } catch {
      return undefined;
    }
  });

  const text = $derived(picked ? report.source.slice(picked.pos[0], picked.pos[1]) : "");
  /** The function's failure, where it attached to the selected site. */
  const failure = $derived(fn.failure && fn.failure.at === at ? fn.failure : null);
</script>

<section class="selection">
  {#if fn.candidateMissing}
    <!-- No claims at all for this function: its contract comes first, since
         every point claim is checked against it. -->
    <header>
      <span class="what">no candidate</span>
      <span class="status">{fn.detail ?? ""}</span>
    </header>
    {#if candidate}
      <FunctionContract {fn} {busy} onsubmit={oncontract} />
    {/if}
  {:else if !picked}
    <p class="empty">
      Select a claim in the source to see its span, its type and the producer's
      own encoding.
    </p>
  {:else}
    <header>
      <span class="what">{picked.kind}</span>
      <span class="span">[{picked.pos[0]},{picked.pos[1]})</span>
      <span class="status">{proofLabel(fn.status)}</span>
    </header>

    {#if text}
      <pre class="text">{text}</pre>
    {/if}

    {#if picked.kind === "result"}
      <dl>
        <dt>must establish</dt>
        <dd class="type">{picked.type}</dd>
      </dl>
      <p class="gap">
        The function's claimed result. Every return is checked against it, and
        completing without returning has to establish it too.
      </p>
    {:else if picked.kind === "expression"}
      <dl>
        <dt>claims</dt>
        <dd class="type">{picked.type}</dd>
      </dl>
    {:else if picked.kind === "environment"}
      <dl>
        {#each picked.bindings as b (b.name)}
          <dt class:changed={picked.changed.has(b.name)}>{b.name}</dt>
          <dd class="type">{b.type}</dd>
        {/each}
      </dl>
    {:else if picked.claims}
      <p class="gap">
        The producer visited this place and claimed nothing here. A claim can be
        added; an attachment site is not necessarily a required obligation.
      </p>
    {:else}
      <p class="gap">{picked.detail}</p>
    {/if}

    {#if failure}
      <!-- Search found no derivation. That is never a statement that the claim
           is false, so it is reported as what happened, not as a verdict. -->
      <p class="failure">{failure.detail}</p>
    {/if}

    {#if candidate && site}
      <ClaimEditor
        kind={site.kind}
        {current}
        {busy}
        onapply={(value) =>
          picked.kind === "unclaimed" ? onadd(site, value) : onapply(site, value)}
      />
    {/if}

    {#if picked.kind === "expression" && picked.raw}
      <details>
        <summary>producer encoding</summary>
        <pre class="raw">{picked.raw}</pre>
      </details>
    {/if}
  {/if}
</section>

<style>
  .selection {
    border-top: 1px solid var(--rule);
    padding: 12px 16px 16px;
    overflow-y: auto;
    max-height: 40vh;
    background: var(--panel);
  }
  .empty {
    margin: 0;
    color: var(--faint);
  }
  header {
    display: flex;
    align-items: baseline;
    gap: 12px;
    margin-bottom: 8px;
  }
  .what {
    font-weight: 600;
    letter-spacing: 0.02em;
  }
  .span,
  .status {
    color: var(--faint);
    font-family: ui-monospace, SFMono-Regular, Menlo, monospace;
    font-size: 11px;
  }
  pre {
    margin: 0 0 10px;
    font:
      12px/1.5 ui-monospace,
      SFMono-Regular,
      Menlo,
      monospace;
    white-space: pre-wrap;
    overflow-x: auto;
  }
  .text {
    color: var(--ink);
    background: var(--field);
    border-radius: 5px;
    padding: 8px 10px;
  }
  dl {
    display: grid;
    grid-template-columns: max-content 1fr;
    gap: 4px 14px;
    margin: 0 0 10px;
    font:
      12px/1.5 ui-monospace,
      SFMono-Regular,
      Menlo,
      monospace;
  }
  dt {
    color: var(--faint);
  }
  dt.changed {
    color: var(--accent);
  }
  dd {
    margin: 0;
    color: var(--claim);
  }
  .failure {
    margin: 0 0 10px;
    color: var(--bad);
  }
  .gap {
    margin: 0 0 10px;
    max-width: 68ch;
    color: var(--faint);
  }
  summary {
    cursor: pointer;
    color: var(--faint);
    font-size: 12px;
  }
  .raw {
    margin-top: 6px;
    color: var(--faint);
    max-height: 220px;
    overflow: auto;
  }
</style>
