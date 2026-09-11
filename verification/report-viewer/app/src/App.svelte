<script lang="ts">
  /*
   * The reader.
   *
   * One line of status, the functions down the left, the source in the middle,
   * and the selected claim beneath it. Everything on screen is a view of one
   * file read through one producer; nothing here decides an outcome.
   */
  import { onMount } from "svelte";
  import FunctionList from "./FunctionList.svelte";
  import Obligation from "./Obligation.svelte";
  import Provenance from "./Provenance.svelte";
  import Selection from "./Selection.svelte";
  import SourceView from "./SourceView.svelte";
  import { reader } from "./state.svelte.ts";
  import type { Producer } from "../../types.ts";

  const PRODUCERS: { value: Producer; label: string }[] = [
    { value: "skjs", label: "SKJS claims" },
    { value: "tsc", label: "TypeScript claims" },
  ];

  onMount(async () => {
    await reader.start();
    const wanted = new URLSearchParams(location.search).get("file");
    const first = reader.groups[0]?.files[0];
    if (wanted || first) await reader.open(wanted || first!);
  });

  function choose(path: string) {
    reader.open(path);
    const url = new URL(location.href);
    url.searchParams.set("file", path);
    history.replaceState(null, "", url);
  }

  const name = $derived(reader.path.split("/").pop() ?? "");
</script>

<div class="app">
  <header class="bar">
    <select
      aria-label="Source file"
      value={reader.path}
      onchange={(e) => choose(e.currentTarget.value)}
      disabled={reader.busy}
    >
      {#each reader.groups as group (group.label)}
        <optgroup label={group.label}>
          {#each group.files as file (file)}
            <option value={file}>{file.split("/").pop()}</option>
          {/each}
        </optgroup>
      {/each}
    </select>

    <select
      aria-label="Claim producer"
      value={reader.producer}
      onchange={(e) =>
        reader.open(reader.path, e.currentTarget.value as Producer)}
      disabled={reader.busy || !reader.path}
    >
      {#each PRODUCERS as p (p.value)}
        <option value={p.value}>{p.label}</option>
      {/each}
    </select>

    <span class="path" title={reader.path}>{name}</span>

    <span class="spacer"></span>

    {#if reader.busy}
      <span class="note">collecting…</span>
    {:else if reader.collection}
      <span class="note">
        {reader.collection.producer} · {Math.round(
          reader.collection.durationMs,
        )}ms
        {#if !reader.collection.verified}· not checked{/if}
      </span>
    {/if}
    {#if !reader.hasVerifier}
      <span class="warn">no verifier built — nothing can be checked</span>
    {/if}
  </header>

  {#if reader.error}
    <p class="error" role="status">{reader.error}</p>
  {/if}

  {#if reader.report && reader.selected}
    {@const report = reader.report}
    {@const fn = reader.selected}
    <div class="body">
      <FunctionList
        functions={reader.functions}
        collection={reader.collection}
        selectedId={fn.id}
        onselect={(id) => reader.select(id)}
      />
      <div class="centre">
        <div class="scroll">
          <SourceView
            {report}
            {fn}
            selectedMark={reader.selection?.markId ?? null}
            unsupported={reader.showUnsupported}
            producerErrors={reader.showProducerErrors}
            onselect={(markId) => reader.select(fn.id, markId)}
          />
        </div>
        <div class="dock">
          <Selection {report} {fn} markId={reader.selection?.markId ?? null} />
          <Obligation
            {fn}
            source={report.source}
            onselect={(offset) => reader.selectAt(fn, offset)}
          />
          <Provenance bundle={reader.bundle} collection={reader.collection} />
        </div>
      </div>
    </div>
  {:else if !reader.busy && !reader.error}
    <p class="empty">Choose a source to collect and check its claims.</p>
  {/if}
</div>

<style>
  .app {
    display: flex;
    flex-direction: column;
    height: 100vh;
    background: var(--page);
    color: var(--ink);
  }
  .bar {
    display: flex;
    align-items: center;
    gap: 10px;
    padding: 8px 14px;
    border-bottom: 1px solid var(--rule);
    background: var(--panel);
    flex: none;
  }
  .bar select {
    font: inherit;
    padding: 4px 8px;
    border: 1px solid var(--rule);
    border-radius: 5px;
    background: var(--field);
    color: var(--ink);
  }
  .path {
    font-family: ui-monospace, SFMono-Regular, Menlo, monospace;
    color: var(--faint);
  }
  .spacer {
    flex: 1;
  }
  .note {
    color: var(--faint);
    font-variant-numeric: tabular-nums;
  }
  .warn {
    color: var(--warn);
  }
  .error {
    margin: 0;
    padding: 8px 14px;
    background: var(--bad-bg);
    color: var(--bad);
  }
  .body {
    display: grid;
    grid-template-columns: minmax(180px, 16rem) 1fr;
    min-height: 0;
    flex: 1;
  }
  .centre {
    display: grid;
    /* The dock takes only what it needs: an empty one is a prompt, not a
       third of the screen. */
    grid-template-rows: minmax(0, 1fr) auto;
    min-height: 0;
    min-width: 0;
  }
  .scroll {
    overflow: auto;
    min-height: 0;
  }
  .dock {
    overflow-y: auto;
    max-height: 45vh;
  }
  .empty {
    padding: 20px 16px;
    color: var(--faint);
  }
  @media (max-width: 760px) {
    .body {
      grid-template-columns: 1fr;
    }
  }
</style>
