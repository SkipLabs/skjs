<script lang="ts">
  /*
   * The functions of the file, each with the two outcomes that matter: what the
   * producer concluded, and what proof search found over the claims it made.
   * They are different questions, so neither stands for the other.
   */
  import { outcome } from "../../marks.mts";
  import type { ShownFunction } from "../../model.mts";
  import type { CollectionRun } from "../../types.ts";

  let {
    functions,
    collection,
    selectedId,
    onselect,
  }: {
    functions: ShownFunction[];
    collection: CollectionRun | null;
    selectedId: string | undefined;
    onselect: (id: string) => void;
  } = $props();

  let filter = $state("");
  const shown = $derived(
    filter
      ? functions.filter((f) =>
          f.name.toLowerCase().includes(filter.toLowerCase()),
        )
      : functions,
  );
</script>

<div class="rail">
  <label class="find">
    <span class="sr">Find function</span>
    <input type="search" bind:value={filter} placeholder="Find function…" />
  </label>

  <ul>
    {#each shown as fn (fn.id)}
      {@const verdict = outcome(fn, collection)}
      <li>
        <button
          class:selected={fn.id === selectedId}
          class:disagrees={verdict.disagrees}
          onclick={() => onselect(fn.id)}
        >
          <span class="name">{fn.name}</span>
          <span class="verdict">
            <span
              class="sym"
              class:good={verdict.producer[0] === "✓"}
              class:bad={verdict.producer[0] === "✗"}
              title="the producer's own outcome: {verdict.producer[1]}"
              >{verdict.producer[0]}</span
            ><span class="arrow">→</span><span
              class="sym"
              class:good={verdict.proof[0] === "✓"}
              class:bad={verdict.proof[0] === "✗"}
              title="what proof search found: {verdict.proof[1]}"
              >{verdict.proof[0]}</span
            >
          </span>
        </button>
      </li>
    {:else}
      <li class="empty">
        {functions.length ? "No function matches." : "No functions."}
      </li>
    {/each}
  </ul>
</div>

<style>
  .rail {
    display: flex;
    flex-direction: column;
    min-height: 0;
    border-right: 1px solid var(--rule);
  }
  .find {
    padding: 10px 12px;
    border-bottom: 1px solid var(--rule);
  }
  .find input {
    width: 100%;
    font: inherit;
    padding: 5px 8px;
    border: 1px solid var(--rule);
    border-radius: 5px;
    background: var(--field);
    color: var(--ink);
  }
  .sr {
    position: absolute;
    width: 1px;
    height: 1px;
    overflow: hidden;
    clip-path: inset(50%);
  }
  ul {
    list-style: none;
    margin: 0;
    padding: 4px 0;
    overflow-y: auto;
    flex: 1;
  }
  li button {
    display: flex;
    align-items: baseline;
    justify-content: space-between;
    gap: 10px;
    width: 100%;
    font: inherit;
    text-align: left;
    padding: 5px 12px;
    background: none;
    border: 0;
    border-left: 2px solid transparent;
    color: var(--ink);
    cursor: pointer;
  }
  li button:hover {
    background: var(--hover);
  }
  li button.selected {
    background: var(--accent-bg);
    border-left-color: var(--accent);
  }
  /* Amber where the two outcomes disagree: the producer accepted something
     nothing could prove, or rejected one a checked certificate covers. */
  li button.disagrees .verdict {
    color: var(--warn);
  }
  .name {
    font-family: ui-monospace, SFMono-Regular, Menlo, monospace;
    overflow: hidden;
    text-overflow: ellipsis;
    white-space: nowrap;
  }
  .verdict {
    flex: none;
    font-variant-numeric: tabular-nums;
    color: var(--faint);
  }
  .arrow {
    padding: 0 2px;
    color: var(--faint);
  }
  .sym.good {
    color: var(--good);
  }
  .sym.bad {
    color: var(--bad);
  }
  .empty {
    padding: 10px 12px;
    color: var(--faint);
  }
</style>
