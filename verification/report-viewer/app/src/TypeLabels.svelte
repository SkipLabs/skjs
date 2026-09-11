<script lang="ts">
  /*
   * The document's own type table, so a label can be written.
   *
   * A normalized claim is a list of indices into this table — `[1, 2]` is
   * `true | false` — and there is no way to write one without seeing what the
   * indices mean. The first four rows are always the primitives; every other
   * row is a clause the file mentioned, interned on first use.
   *
   * Naming a type that is not already a row would mean interning it, which is
   * the producer's job. So this shows what can be named, and nothing more.
   */
  import reader from "../../obligation.js";

  let { types }: { types: unknown[] } = $props();

  const rows = $derived(
    types.map((_, label) => ({
      label,
      text: reader.typeText(types, [label]),
    })),
  );
</script>

<div class="labels">
  <span class="lead">labels</span>
  <ul>
    {#each rows as row (row.label)}
      <li><b>{row.label}</b> {row.text}</li>
    {/each}
  </ul>
</div>

<style>
  .labels {
    display: flex;
    gap: 10px;
    margin-top: 6px;
    font:
      11px/1.6 ui-monospace,
      SFMono-Regular,
      Menlo,
      monospace;
  }
  .lead {
    flex: none;
    color: var(--faint);
  }
  ul {
    display: flex;
    flex-wrap: wrap;
    gap: 4px 14px;
    list-style: none;
    margin: 0;
    padding: 0;
  }
  li {
    color: var(--claim);
  }
  b {
    color: var(--faint);
    font-weight: 400;
    padding-right: 3px;
  }
</style>
