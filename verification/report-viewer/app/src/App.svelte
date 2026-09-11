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
  import OpenPath from "./OpenPath.svelte";
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
    const params = new URLSearchParams(location.search);
    const wanted = params.get("file");
    const producer = params.get("producer") === "tsc" ? "tsc" : "skjs";
    const first = reader.groups[0]?.files[0];
    if (wanted || first) await reader.open(wanted || first!, producer);
    // A link may name a claim. It names a record of one snapshot, so it is
    // honoured where it still resolves and dropped where it does not.
    const [fnName, markId] = (location.hash.slice(1) || "").split(":");
    const fn = reader.functions.find((f) => f.name === fnName);
    if (fn && markId) reader.select(fn.id, markId);
  });

  function choose(path: string) {
    reader.open(path);
  }

  /*
   * The address bar follows the view: the file, the producer, and the selected
   * claim. Reopening the link restores the same view. Ids identify records
   * within one snapshot, not the same claim across collections, so a link into
   * a report that has changed may name nothing — and then the reader leaves the
   * selection alone rather than guessing.
   */
  $effect(() => {
    if (!reader.path) return;
    const url = new URL(location.href);
    url.searchParams.set("file", reader.path);
    url.searchParams.set("producer", reader.producer);
    const fn = reader.selected;
    const mark = reader.selection?.markId;
    url.hash = fn && mark ? `${fn.name}:${mark}` : "";
    history.replaceState(null, "", url.toString());
  });

  /*
   * Selecting a claim puts the cursor in its editor, so stepping between claims
   * needs a key the editor will not take: Alt with the arrows, or with j and k,
   * works while typing and leaves the next claim ready to type into. The
   * letters are matched by physical key, because Option composes characters on
   * macOS and would otherwise arrive as ∆ and ˚.
   */
  function onkeydown(event: KeyboardEvent) {
    if (!reader.report) return;
    if (event.altKey && !event.metaKey && !event.ctrlKey) {
      const by =
        event.key === "ArrowDown" || event.code === "KeyJ"
          ? 1
          : event.key === "ArrowUp" || event.code === "KeyK"
            ? -1
            : 0;
      if (by) {
        event.preventDefault();
        reader.step(by as 1 | -1);
      }
      return;
    }
    if (event.metaKey || event.ctrlKey || event.altKey) return;
    const target = event.target as HTMLElement | null;
    if (
      target?.isContentEditable ||
      ["INPUT", "TEXTAREA", "SELECT", "BUTTON"].includes(target?.tagName ?? "")
    )
      return;
    const moves: Record<string, () => void> = {
      j: () => reader.step(1),
      ArrowDown: () => reader.step(1),
      k: () => reader.step(-1),
      ArrowUp: () => reader.step(-1),
      "]": () => reader.stepFunction(1),
      "[": () => reader.stepFunction(-1),
      Escape: () => reader.selection && reader.select(reader.selection.functionId),
    };
    const move = moves[event.key];
    if (move) {
      event.preventDefault();
      move();
    }
  }

  const name = $derived(reader.path.split("/").pop() ?? "");
</script>

<svelte:window {onkeydown} />

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

    <OpenPath busy={reader.busy} onopen={choose} />

    <!-- What the source view draws beyond the claims themselves. Both are off
         by default: they answer questions about the producer's run, not about
         what it claims. -->
    <label class="tick">
      <input type="checkbox" bind:checked={reader.showProducerErrors} />
      producer diagnostics
    </label>
    <label class="tick">
      <input type="checkbox" bind:checked={reader.showUnsupported} />
      undecoded bindings
    </label>

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
    {#if reader.edited}
      <!-- A draft lives beside the source, named after it, the way the
           command-line tools already name what they write. There is nothing to
           choose and nothing to find: reopening the source finds it. -->
      <button
        class="plain"
        onclick={() => reader.keep()}
        disabled={reader.busy}
        title="writes the candidate beside the source, for the CLI to read too"
        >keep this draft</button
      >
      <button
        class="plain"
        onclick={() => reader.restore()}
        disabled={reader.busy}>restore the producer's claims</button
      >
    {/if}
    {#if reader.draftPath}
      <span class="note" title={reader.draftPath}>draft beside the source</span>
      <button
        class="plain"
        onclick={() => reader.discard()}
        disabled={reader.busy}
        title="deletes {reader.draftPath}">discard it</button
      >
    {/if}
    {#if !reader.hasVerifier}
      <span class="warn">no verifier built — nothing can be checked</span>
    {/if}
  </header>

  {#if reader.error}
    <p class="error" role="status">{reader.error}</p>
  {/if}
  {#if reader.staleDraft}
    <p class="stale" role="status">{reader.staleDraft}</p>
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
          <Selection
            {report}
            {fn}
            markId={reader.selection?.markId ?? null}
            candidate={reader.candidate}
            busy={reader.busy}
            onapply={(site, value) => reader.apply(fn, site, value)}
            onadd={(site, value) => reader.add(fn, site, value)}
            oncontract={(contract) => reader.addContract(fn, contract)}
          />
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
  .tick {
    display: inline-flex;
    align-items: center;
    gap: 5px;
    color: var(--faint);
    white-space: nowrap;
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
  .plain {
    padding: 3px 10px;
    border: 1px solid var(--rule);
    border-radius: 5px;
    background: var(--field);
    color: var(--ink);
    cursor: pointer;
  }
  .error {
    margin: 0;
    padding: 8px 14px;
    background: var(--bad-bg);
    color: var(--bad);
  }
  .stale {
    margin: 0;
    padding: 8px 14px;
    color: var(--warn);
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
