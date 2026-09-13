<script lang="ts">
  /*
   * Why verification stopped.
   *
   * What the verifier had, and what had to follow from it. This is explanatory
   * metadata about an unsuccessful attempt: it is never evidence, and it never
   * says a claim is false. The role is taken from the record rather than
   * guessed from the span — a return contract and the returned expression's own
   * claim share a span and are different obligations — and where the record
   * names no specific role, this says nothing rather than inventing one.
   */
  import type { ObligationView } from "../../../tools/obligation-view.mts";
  import type { ShownFunction } from "../../model.mts";

  let {
    fn,
    source,
    onselect,
  }: {
    fn: ShownFunction;
    source: string;
    /** Jump to one end of an edge, by source offset. */
    onselect: (offset: number) => void;
  } = $props();

  const view = $derived<ObligationView | null>(
    fn.obligationView ?? null,
  );
</script>

{#if view}
  <section class="why">
    <header>
      <h2>{view.title || view.kindLabel}</h2>
      <span class="meta">{view.kindLabel}</span>
    </header>

    {#if view.what}
      <p class="what">{view.what}</p>
    {/if}

    {#if view.judgement}
      <pre class="sequent">{view.judgement.text}</pre>
      <details>
        <summary>Type graph (exact row definitions)</summary>
        {#each view.graph as row (row.label)}
          <div class="type">{row.label} = {row.definition}</div>
        {/each}
      </details>
    {/if}

    {#if view.rows.length}
      <table>
        <caption>{view.kind === "edge-coverage" ? "Carried and required context" : "Context"}</caption>
        <thead>
          <tr><th>binding</th><th>carried</th>{#if view.kind === "edge-coverage"}<th>required</th>{/if}</tr>
        </thead>
        <tbody>
          {#each view.rows as row (row.slot)}
            <tr class:differs={row.differs}>
              <td class="name">{row.binding}</td>
              <td class="type">{row.have}</td>
              {#if view.kind === "edge-coverage"}<td class="type">{row.need}</td>{/if}
            </tr>
          {/each}
        </tbody>
      </table>
    {/if}

    {#if view.conclusion}
      <dl>
        {#if view.term}<dt>term</dt>
          <dd class="type">{view.term}</dd>{/if}
        <dt>had to conclude</dt>
        <dd class="type">{view.conclusion}</dd>
      </dl>
    {/if}

    {#if view.knowledge.length}
      <ul class="facts">
        {#each view.knowledge as k (k.slot)}
          <li><span class="name">{k.binding}</span> {k.what}</li>
        {/each}
      </ul>
    {/if}

    {#if view.observation}
      <p class="observation">{view.observation}</p>
    {/if}

    {#if view.endpoints.length}
      <p class="ends">
        {#each view.endpoints as end (end.end)}
          {@const at = end.sourceMap?.pos?.[0]}
          <button
            disabled={at === undefined}
            onclick={() => at !== undefined && onselect(at)}
          >
            {end.end === "from" ? "from" : "to"}
            {end.sourceMap?.role ? `· ${end.sourceMap.role}` : ""}
          </button>
        {/each}
      </p>
    {/if}

    {#if view.note}
      <p class="note">{view.note}</p>
    {/if}

    <!-- What the number means, rather than the number on its own. A search
         that ran out of budget stopped looking; it did not conclude. -->
    <p class="budget">
      Proof search was given a budget of {view.fuel}. Failing within it means no
      derivation was found, never that the claim is false.
    </p>
  </section>
{/if}

<style>
  .sequent { white-space: pre-wrap; overflow-wrap: anywhere; font-size: 12px; }
  .why {
    border-top: 1px solid var(--rule);
    padding: 12px 16px 16px;
    background: var(--panel);
  }
  header {
    display: flex;
    align-items: baseline;
    gap: 12px;
  }
  h2 {
    margin: 0;
    font-size: 13px;
    font-weight: 600;
    color: var(--bad);
  }
  .meta {
    color: var(--faint);
    font-size: 11px;
    font-family: ui-monospace, SFMono-Regular, Menlo, monospace;
  }
  .budget {
    margin: 10px 0 0;
    max-width: 68ch;
    color: var(--faint);
    font-size: 12px;
  }
  .what,
  .note,
  .observation {
    margin: 6px 0 10px;
    max-width: 68ch;
    color: var(--faint);
  }
  .observation {
    color: var(--ink);
  }
  table {
    border-collapse: collapse;
    margin: 0 0 10px;
    font:
      12px/1.5 ui-monospace,
      SFMono-Regular,
      Menlo,
      monospace;
  }
  caption {
    text-align: left;
    color: var(--faint);
    padding-bottom: 4px;
  }
  th {
    text-align: left;
    font-weight: 400;
    color: var(--faint);
    padding-right: 20px;
  }
  td {
    padding-right: 20px;
    vertical-align: top;
  }
  .name {
    color: var(--faint);
  }
  .type {
    color: var(--claim);
  }
  /* The bindings that differ are the ones the edge could not carry across. */
  tr.differs .name,
  tr.differs .type {
    color: var(--bad);
  }
  dl {
    display: grid;
    grid-template-columns: max-content 1fr;
    gap: 3px 14px;
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
  dd {
    margin: 0;
    color: var(--claim);
  }
  .facts {
    list-style: none;
    margin: 0 0 10px;
    padding: 0;
    font:
      12px/1.6 ui-monospace,
      SFMono-Regular,
      Menlo,
      monospace;
    color: var(--claim);
  }
  .ends {
    display: flex;
    gap: 8px;
    margin: 0 0 8px;
  }
  .ends button {
    font: inherit;
    padding: 3px 10px;
    border: 1px solid var(--rule);
    border-radius: 5px;
    background: var(--field);
    color: var(--ink);
    cursor: pointer;
  }
  .ends button:disabled {
    color: var(--faint);
    cursor: default;
  }
</style>
