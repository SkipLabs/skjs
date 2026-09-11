<script lang="ts">
  /*
   * Choosing a type, where the encoding is a list of labels.
   *
   * A normalized claim indexes the document's own type table, and the indices
   * are an implementation detail of that document — nothing a person should be
   * asked to write. So the table is offered by the names it holds, and the
   * claim is the set chosen: picking `true` and `false` is the union of the
   * two, and picking nothing is the empty union, which is `never`.
   *
   * Only rows already in the table can be chosen. Naming a type that is not one
   * would mean interning it, and that is the producer's job, not the reader's —
   * so there is nothing here that can express it, rather than a field that
   * takes it and fails later.
   */
  import reader from "../../obligation.mts";

  let {
    types,
    selected,
    onchange,
  }: {
    types: unknown[];
    /** The chosen rows, as the encoding holds them. */
    selected: number[];
    onchange: (labels: number[]) => void;
  } = $props();

  const rows = $derived(
    types.map((_, label) => ({ label, text: reader.typeText(types, [label]) })),
  );

  function toggle(label: number) {
    const next = selected.includes(label)
      ? selected.filter((l) => l !== label)
      : [...selected, label];
    // The format holds labels ascending; a claim is a set, not a sequence.
    onchange(next.sort((a, b) => a - b));
  }
</script>

<div class="chooser">
  <ul>
    {#each rows as row (row.label)}
      <li>
        <button
          type="button"
          class:on={selected.includes(row.label)}
          onclick={() => toggle(row.label)}
        >
          {row.text}
        </button>
      </li>
    {/each}
  </ul>
  <p class="reading">
    {selected.length
      ? reader.typeText(types, selected)
      : "never — nothing chosen is the empty union"}
  </p>
</div>

<style>
  .chooser {
    display: grid;
    gap: 6px;
  }
  ul {
    display: flex;
    flex-wrap: wrap;
    gap: 5px;
    list-style: none;
    margin: 0;
    padding: 0;
  }
  button {
    font:
      12px/1.4 ui-monospace,
      SFMono-Regular,
      Menlo,
      monospace;
    padding: 3px 9px;
    border: 1px solid var(--rule);
    border-radius: 999px;
    background: var(--field);
    color: var(--faint);
    cursor: pointer;
  }
  button:hover {
    border-color: var(--claim-edge);
  }
  button.on {
    background: var(--claim-bg);
    border-color: var(--claim-edge);
    color: var(--claim);
  }
  .reading {
    margin: 0;
    font:
      12px/1.5 ui-monospace,
      SFMono-Regular,
      Menlo,
      monospace;
    color: var(--claim);
  }
</style>
