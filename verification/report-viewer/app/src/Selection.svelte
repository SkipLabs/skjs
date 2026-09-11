<script lang="ts">
  /*
   * The selected claim, docked under the source it came from.
   *
   * The old reader put this in a side rail, far from the thing clicked. A claim
   * and its detail belong together, so this sits directly beneath the line it
   * is about and the source keeps the full width.
   *
   * Four things can be selected, and each says a different thing: a claim the
   * producer made, the environment at a statement entry, a place it did not
   * visit, and a place it visited but claimed nothing at — which is where a
   * claim can be added.
   */
  import ClaimEditor from "./ClaimEditor.svelte";
  import FunctionContract from "./FunctionContract.svelte";
  import { proofLabel } from "../../marks.mts";
  import { editable, type ClaimSite } from "../../candidate.mts";
  import type { Report, ShownFunction } from "../../model.mts";
  import type { Candidate } from "../../types.ts";

  let {
    report,
    fn,
    markId,
    candidate,
    busy,
    onapply,
    onadd,
    oncontract,
  }: {
    report: Report;
    fn: ShownFunction;
    markId: string | null;
    candidate: Candidate | null;
    busy: boolean;
    onapply: (site: ClaimSite, value: unknown) => void;
    onadd: (site: ClaimSite, value: unknown) => void;
    oncontract: (contract: {
      params: { name: string; type: unknown }[];
      result: unknown;
    }) => void;
  } = $props();

  /** A mark id is a list prefix and an index within that list. */
  const picked = $derived.by(() => {
    if (!markId) return null;
    const kind = markId[0];
    const index = Number(markId.slice(1));
    if (!Number.isInteger(index)) return null;
    if (kind === "e") return { what: "expression", item: fn.exprs[index] };
    if (kind === "n") return { what: "environment", item: fn.entries[index] };
    if (kind === "g") return { what: "gap", item: fn.gaps[index] };
    if (kind === "m")
      return { what: "missing", item: fn.missingSites?.[index] };
    return null;
  });

  /** Where the selected claim sits, in the terms a candidate is addressed by. */
  const site = $derived.by((): ClaimSite | null => {
    const item = picked?.item as
      | { pos?: [number, number]; kind?: string }
      | undefined;
    const pos = item?.pos;
    if (!pos || !picked) return null;
    if (picked.what === "expression") return { kind: "expression", pos };
    if (picked.what === "environment") return { kind: "environment", pos };
    // A missing site names the kind of claim that belongs there.
    if (picked.what === "missing" && item?.kind)
      return { kind: item.kind as ClaimSite["kind"], pos };
    return null;
  });

  /** The candidate's value at the site, as the editor reads and writes it. */
  const current = $derived.by(() => {
    if (!candidate || !site || picked?.what === "missing") return undefined;
    try {
      return editable(candidate, fn, site);
    } catch {
      return undefined;
    }
  });

  const text = $derived.by(() => {
    const pos = (picked?.item as { pos?: [number, number] })?.pos;
    return pos ? report.source.slice(pos[0], pos[1]) : "";
  });
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
  {:else if !picked?.item}
    <p class="empty">
      Select a claim in the source to see its span, its type and the producer's
      own encoding.
    </p>
  {:else}
    {@const item = picked.item as Record<string, any>}
    <header>
      <span class="what">{picked.what}</span>
      {#if item.pos}
        <span class="span">[{item.pos[0]},{item.pos[1]})</span>
      {/if}
      <span class="status">{proofLabel(fn.status)}</span>
    </header>

    {#if text}
      <pre class="text">{text}</pre>
    {/if}

    {#if picked.what === "expression"}
      <dl>
        <dt>claims</dt>
        <dd class="type">{item.type}</dd>
      </dl>
    {:else if picked.what === "environment"}
      <dl>
        {#each item.bindings ?? [] as b (b.name)}
          <dt class:changed={item.changed?.has(b.name)}>{b.name}</dt>
          <dd class="type">{b.type}</dd>
        {/each}
      </dl>
    {:else if picked.what === "missing"}
      <p class="gap">
        The producer visited this place and claimed nothing here. A claim can be
        added; an attachment site is not necessarily a required obligation.
      </p>
    {:else}
      <p class="gap">{item.detail}</p>
    {/if}

    {#if item.failure}
      <!-- Search found no derivation. That is never a statement that the claim
           is false, so it is reported as what happened, not as a verdict. -->
      <p class="failure">{item.failure}</p>
    {/if}

    {#if candidate && site}
      <ClaimEditor
        kind={site.kind}
        {current}
        {busy}
        onapply={(value) =>
          picked.what === "missing" ? onadd(site, value) : onapply(site, value)}
      />
    {/if}

    {#if item.raw}
      <details>
        <summary>producer encoding</summary>
        <pre class="raw">{item.raw}</pre>
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
