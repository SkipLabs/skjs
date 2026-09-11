<script lang="ts">
  /*
   * Opening any repository source.
   *
   * The example groups are a starting point, not the limit of what can be read:
   * any `.ts` path in the repository can be collected and checked. Suggestions
   * come from the server, which refuses paths outside the repository, so this
   * offers what exists rather than deciding what is allowed.
   */
  import { sources } from "./api.ts";

  let { busy, onopen }: { busy: boolean; onopen: (path: string) => void } =
    $props();

  let query = $state("");
  let matches = $state<string[]>([]);
  let total = $state(0);
  let open = $state(false);

  $effect(() => {
    const q = query.trim();
    if (!q) {
      matches = [];
      total = 0;
      return;
    }
    // The listing is a convenience; a full path works whether or not it is
    // suggested, so a failed lookup is not an error.
    let live = true;
    sources(q)
      .then((r) => {
        if (!live) return;
        matches = r.files;
        total = r.total;
      })
      .catch(() => {
        if (live) matches = [];
      });
    return () => {
      live = false;
    };
  });

  function choose(path: string) {
    query = "";
    open = false;
    onopen(path);
  }
</script>

<div class="open">
  <input
    type="search"
    bind:value={query}
    onfocus={() => (open = true)}
    onblur={() => setTimeout(() => (open = false), 150)}
    onkeydown={(e) => {
      if (e.key === "Enter" && query.trim()) choose(query.trim());
      if (e.key === "Escape") open = false;
    }}
    placeholder="Open any repository path…"
    aria-label="Repository source path"
    spellcheck="false"
    disabled={busy}
  />
  {#if open && matches.length}
    <ul class="suggestions">
      {#each matches.slice(0, 12) as file (file)}
        <li>
          <button type="button" onmousedown={() => choose(file)}>{file}</button>
        </li>
      {/each}
      {#if total > 12}
        <li class="more">{total - 12} more — narrow the search</li>
      {/if}
    </ul>
  {/if}
</div>

<style>
  .open {
    position: relative;
  }
  input {
    font: inherit;
    width: 16rem;
    padding: 4px 8px;
    border: 1px solid var(--rule);
    border-radius: 5px;
    background: var(--field);
    color: var(--ink);
  }
  .suggestions {
    position: absolute;
    z-index: 5;
    top: calc(100% + 4px);
    left: 0;
    min-width: 28rem;
    max-height: 18rem;
    overflow-y: auto;
    list-style: none;
    margin: 0;
    padding: 4px;
    border: 1px solid var(--rule);
    border-radius: 6px;
    background: var(--panel);
    box-shadow: 0 6px 20px rgb(0 0 0 / 0.14);
  }
  .suggestions button {
    display: block;
    width: 100%;
    text-align: left;
    font:
      12px/1.5 ui-monospace,
      SFMono-Regular,
      Menlo,
      monospace;
    padding: 4px 8px;
    border: 0;
    border-radius: 4px;
    background: none;
    color: var(--ink);
    cursor: pointer;
  }
  .suggestions button:hover {
    background: var(--hover);
  }
  .more {
    padding: 4px 8px;
    color: var(--faint);
  }
</style>
