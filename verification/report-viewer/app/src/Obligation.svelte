<script lang="ts">
  // The report writer names values and prepares the comparison. The panel only
  // renders it; the exact sequent remains available alongside that explanation.
  import type { ShownFunction } from "../../model.mts";
  import { formatJudgement } from "../../../tools/diagnostic-view.mts";
  let { fn, onselect }: {
    fn: ShownFunction;
    onselect: (offset: number) => void;
  } = $props();
  const view = $derived(fn.obligationView ?? null);
</script>

{#if view}
  <section class="why" aria-label="Failed obligation">
    <h2>{view.title || view.kindLabel}</h2>
    <p class="explanation">{view.summary || view.what}</p>

    {#if view.focus}
      <div class="table-scroll">
        <table class="comparison">
          <caption>Type requirement for <code>{view.focus.subject}</code></caption>
          <thead><tr>
            <th scope="col">Available claim</th>
            <th scope="col">{view.focus.requiredLabel}</th>
          </tr></thead>
          <tbody><tr>
            <td><code>{view.focus.available}</code></td>
            <td class="required"><code>{view.focus.required}</code></td>
          </tr></tbody>
        </table>
      </div>
    {/if}

    {#if view.knowledge.length}
      <ul class="facts">
        {#each view.knowledge as k}
          <li>Required: <code>{k.binding}</code> {k.what}</li>
        {/each}
      </ul>
    {/if}
    {#if view.observation}<p>{view.observation}</p>{/if}
    <p class="status">{view.searchOutcome}</p>

    {#if view.rows.length}
      <details>
        <summary>Full context ({view.rows.length} bindings)</summary>
        <div class="table-scroll">
          <table>
            <caption>{view.kind === "edge-coverage" ? "Incoming and destination claims" : "Assumptions available at this point"}</caption>
            <thead><tr>
              <th scope="col">Binding</th>
              <th scope="col">Available type</th>
              {#if view.kind === "edge-coverage"}<th scope="col">Required type</th>{/if}
            </tr></thead>
            <tbody>
              {#each view.rows as row (row.slot)}
                <tr class:focused={row.binding === view.focus?.subject}>
                  <th scope="row"><code>{row.binding}</code></th>
                  <td><code>{row.have}</code></td>
                  {#if view.kind === "edge-coverage"}<td><code>{row.need}</code></td>{/if}
                </tr>
              {/each}
            </tbody>
          </table>
        </div>
        {#if view.namedConclusion}
          <p class="conclusion">Required conclusion: <code>⊢ {view.namedConclusion}</code></p>
        {/if}
        {#if view.note}<p class="note">{view.note}</p>{/if}
      </details>
    {/if}

    <details class="technical">
      <summary>Exact obligation and type graph</summary>
      <p class="meta">{view.kindLabel} · {view.id} · {view.phase}</p>
      {#if view.judgement}<pre>{formatJudgement(view.judgement)}</pre>{/if}
      <div class="table-scroll">
        <table>
          <caption>Exact type graph</caption>
          <thead><tr><th scope="col">Label</th><th scope="col">Definition</th></tr></thead>
          <tbody>{#each view.graph as row (row.label)}
            <tr><th scope="row"><code>{row.label}</code></th><td><code>{row.definition}</code></td></tr>
          {/each}</tbody>
        </table>
      </div>
    </details>

    {#if view.endpoints.length}
      <div class="ends">
        {#each view.endpoints as end (end.end)}
          {@const at = end.sourceMap?.pos?.[0]}
          <button disabled={at === undefined} onclick={() => at !== undefined && onselect(at)}>
            {end.end === "from" ? "Incoming point" : "Destination"}
          </button>
        {/each}
      </div>
    {/if}
  </section>
{/if}

<style>
  .why { border-top: 1px solid var(--rule); padding: 16px; background: var(--panel); font-size: 13px; line-height: 1.55; }
  h2 { margin: 0 0 8px; font-size: 15px; color: var(--bad); }
  p { margin: 8px 0 12px; max-width: 80ch; }
  .explanation { color: var(--ink); }
  .status, .meta, .note { color: var(--faint); font-size: 12px; }
  details { border-top: 1px solid var(--rule); margin-top: 12px; padding-top: 10px; }
  summary { cursor: pointer; color: var(--ink); font-weight: 500; margin-bottom: 8px; }
  .table-scroll { overflow-x: auto; margin: 8px 0 12px; }
  table { width: 100%; border-collapse: collapse; border: 1px solid var(--rule); font-size: 12px; }
  caption { text-align: left; padding: 0 0 8px; color: var(--faint); font-size: 12px; }
  th, td { text-align: left; vertical-align: top; padding: 9px 12px; border: 1px solid var(--rule); }
  thead th { background: var(--field); color: var(--ink); font-weight: 600; white-space: nowrap; }
  tbody th { font-weight: 400; color: var(--ink); }
  td { color: var(--claim); }
  .comparison { table-layout: fixed; }
  .comparison td { font-size: 14px; }
  .required { color: var(--bad); font-weight: 600; }
  .focused { background: var(--field); }
  code { font-family: ui-monospace, SFMono-Regular, Menlo, monospace; overflow-wrap: anywhere; }
  pre { white-space: pre-wrap; overflow-wrap: anywhere; font: 12px/1.6 ui-monospace, SFMono-Regular, Menlo, monospace; padding: 12px; border: 1px solid var(--rule); }
  .facts { padding-left: 20px; }
  .conclusion { color: var(--ink); }
  .ends { display: flex; gap: 8px; margin-top: 12px; }
  .ends button { font: inherit; padding: 5px 10px; border: 1px solid var(--rule); border-radius: 5px; background: var(--field); color: var(--ink); cursor: pointer; }
  .ends button:disabled { color: var(--faint); cursor: default; }
</style>
