<script lang="ts">
  /*
   * The selected claim, docked under the source it came from.
   *
   * The old report viewer put this in a side rail, far from the thing clicked. A claim
   * and its detail belong together, so this sits directly beneath the line it
   * is about and the source keeps the full width.
   *
   * Four kinds of site can be selected: the result the function must
   * establish, an expression claim, an environment, and a place with nothing
   * claimed.
   */
  import { proofLabel } from "../../marks.mts";
  import { rigidAt } from "../../model.mts";
  import type { Report, ShownFunction, Site } from "../../model.mts";

  let {
    report,
    fn,
    site: at,
  }: {
    report: Report;
    fn: ShownFunction;
    /** The selected site's index, in source order. */
    site: number | null;
  } = $props();

  const picked = $derived<Site | null>(at === null ? null : (fn.sites[at] ?? null));

  /*
   * A claim of `T` says the whole type: `T` is rigid, so it has no value and
   * nothing stands for it. What is known about it is the bound the source
   * declares, which is not in the claim at all — it is read from the Fragment,
   * which the verifier reads beside the claims, and it is what discharges
   * `T ≤ boolean`. Showing the claim without it would show one premise of a
   * check and hide the other. Both were printed at report generation; this
   * only asks which of them belong to the selected site.
   */
  const rigid = $derived(picked ? rigidAt(picked) : []);

  const text = $derived(picked ? report.source.slice(picked.pos[0], picked.pos[1]) : "");
  /** The function's failure, where it attached to the selected site. */
  const failure = $derived(fn.failure && fn.failure.at === at ? fn.failure : null);
</script>

<section class="selection">
  {#if fn.claimsMissing}
    <!-- No claims at all for this function. -->
    <header>
      <span class="what">no claims</span>
      <span class="status">{fn.detail ?? ""}</span>
    </header>
  {:else if !picked && !fn.sites.length && fn.detail}
    <!-- Nothing here is claimed, and the unit says why. -->
    <p class="empty">{fn.detail}</p>
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
        The producer visited this place and claimed nothing here. An attachment
        site is not necessarily a required obligation.
      </p>
    {:else}
      <p class="gap">{picked.detail}</p>
    {/if}

    {#if rigid.length}
      <dl class="rigid">
        {#each rigid as p (p.name)}
          <dt>{p.name}</dt>
          <dd class="type">
            {#if p.bound === null}
              no declared bound
            {:else}
              extends {p.bound}
            {/if}
          </dd>
        {/each}
      </dl>
      <p class="gap">
        Declared in the source, not claimed here. A rigid parameter has no
        value; its bound is the whole of what is known about it, and it is what
        a check of this claim against a concrete type has to go through.
      </p>
    {/if}

    {#if failure}
      <!-- Search found no derivation. That is never a statement that the claim
           is false, so it is reported as what happened, not as a verdict. -->
      <p class="failure">{failure.detail}</p>
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
  /* Set apart from the claim above it: the bound is not something the
     producer claimed, and it should not read as though it were. */
  .rigid {
    margin-top: -4px;
    padding-top: 8px;
    border-top: 1px dotted var(--rule);
  }
  .rigid dd {
    color: var(--faint);
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
