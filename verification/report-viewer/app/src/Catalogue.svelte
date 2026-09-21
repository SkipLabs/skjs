<script lang="ts">
  /*
   * The catalogue: every source the reader offers, laid out to be read.
   *
   * It replaces a dropdown of ninety-eight basenames. A dropdown answers
   * "which one was it called", which can only be asked about a file already
   * seen; nothing in it says what a file is about, and two files in different
   * groups can read identically — `cells.ts` is three different sources here.
   * So the group says what it is, the file says what it demonstrates, and the
   * whole set is visible at once rather than behind a control.
   *
   * Nothing here is a verdict. A group's note says whose claim its label makes,
   * and a file listed under a heading is listed, never thereby verified.
   */
  import type { Group } from "./api.ts";

  let {
    groups,
    busy,
    current,
    onopen,
  }: {
    groups: Group[];
    busy: boolean;
    current: string;
    onopen: (path: string) => void;
  } = $props();

  const name = (path: string) => path.split("/").pop() ?? path;
</script>

<div class="catalogue">
  <div class="columns">
    {#each groups as group (group.label)}
      <section>
        <h2>
          {group.label}
          <span class="count">{group.files.length}</span>
        </h2>
        {#if group.note}<p class="note">{group.note}</p>{/if}
        <ul>
          {#each group.files as file (file.path)}
            <li>
              <button
                type="button"
                class:open={file.path === current}
                disabled={busy}
                title={file.path}
                onclick={() => onopen(file.path)}
              >
                <span class="name">{name(file.path)}</span>
                {#if file.about}<span class="about">{file.about}</span>{/if}
              </button>
            </li>
          {/each}
        </ul>
      </section>
    {/each}
  </div>
</div>

<style>
  .catalogue {
    /* The scrolling is here and the columns are inside, deliberately. Flowing
       columns need an auto height to balance into: given a fixed one they
       make further columns off to the side instead, and a container that
       scrolls only downwards then clips them — which hid two whole groups
       while this was being built. A catalogue that quietly omits a third of
       what it lists is worse than the dropdown it replaces. */
    overflow-y: auto;
    padding: 16px 20px 40px;
  }
  .columns {
    /* The groups are wildly uneven — one holds thirty-four files, another one
       — and a grid would give every group in a row the height of the tallest.
       Flowed, they pack. */
    columns: 21rem;
    column-gap: 28px;
  }
  section {
    /* A group is not split across a column break: a heading stranded from its
       files is a group you would read as empty. */
    break-inside: avoid;
    display: inline-block;
    width: 100%;
    margin-bottom: 16px;
  }
  h2 {
    display: flex;
    align-items: baseline;
    gap: 8px;
    margin: 0;
    padding-bottom: 3px;
    border-bottom: 1px solid var(--rule);
    font-size: 13px;
    font-weight: 600;
    color: var(--ink);
  }
  .count {
    font-variant-numeric: tabular-nums;
    font-weight: 400;
    color: var(--faint);
  }
  .note {
    margin: 4px 0 6px;
    font-size: 12px;
    line-height: 1.45;
    color: var(--faint);
  }
  ul {
    list-style: none;
    margin: 0;
    padding: 0;
  }
  button {
    display: flex;
    align-items: baseline;
    gap: 8px;
    width: 100%;
    text-align: left;
    padding: 3px 6px;
    border: 0;
    border-radius: 4px;
    background: none;
    color: var(--ink);
    font: inherit;
    cursor: pointer;
  }
  button:hover:not(:disabled) {
    background: var(--hover);
  }
  button:disabled {
    cursor: default;
    opacity: 0.55;
  }
  button.open {
    background: var(--accent-bg);
  }
  .name {
    flex: none;
    font-family: ui-monospace, SFMono-Regular, Menlo, monospace;
    font-size: 12px;
  }
  .about {
    /* The description is the findable part, so it is allowed to be the long
       one; the name it belongs to stays fixed at the left. */
    flex: 1;
    min-width: 0;
    font-size: 11.5px;
    line-height: 1.5;
    color: var(--faint);
  }
</style>
