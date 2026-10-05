<script lang="ts">
  /*
   * The report viewer.
   *
   * One line of status, the functions down the left, the source in the middle,
   * and the selected claim beneath it. Everything on screen is a view of one
   * file read through the producer; nothing here decides an outcome.
   * What is on screen is one object, state.svelte.ts, which every view reads.
   * Catalogue.svelte is what opens without a file in the link: every example group.
   * FunctionList.svelte lists the file's functions, each with its two outcomes.
   * SourceView.svelte draws the source with each claim under its span.
   * Selection.svelte shows the selected claim beneath the source.
   * Obligation.svelte explains why verification stopped, from the verifier's record.
   * OpenPath.svelte opens any repository path the catalogue does not list.
   * Provenance.svelte states the exact command and its time.
   */
  import { onMount } from "svelte";
  import Catalogue from "./Catalogue.svelte";
  import FunctionList from "./FunctionList.svelte";
  import Obligation from "./Obligation.svelte";
  import OpenPath from "./OpenPath.svelte";
  import Provenance from "./Provenance.svelte";
  import Selection from "./Selection.svelte";
  import SourceView from "./SourceView.svelte";
  import { viewer } from "./state.svelte.ts";

  onMount(async () => {
    // Read the link before opening anything: opening selects afresh, and the
    // address bar follows the selection, so the hash is gone by then.
    const [fnName, at] = (location.hash.slice(1) || "").split(":");
    await viewer.start();
    const params = new URLSearchParams(location.search);
    const wanted = params.get("file");
    // A link that names a file opens it; one that does not shows what there
    // is, rather than opening whichever source happens to be listed first.
    if (wanted) await viewer.open(wanted);
    else viewer.browsing = true;
    // A link may name a claim. It names a record of one snapshot, so it is
    // honoured where it still resolves and dropped where it does not.
    const fn = viewer.functions.find((f) => f.name === fnName);
    const site = Number(at);
    if (fn && Number.isInteger(site) && site >= 0 && site < fn.sites.length)
      viewer.select(fn.id, site);
  });

  function choose(path: string) {
    viewer.open(path);
  }

  /*
   * The address bar follows the view: the file and the selected
   * claim. Reopening the link restores the same view. Ids identify records
   * within one snapshot, not the same claim across collections, so a link into
   * a report that has changed may name nothing — and then the report viewer leaves the
   * selection alone rather than guessing.
   */
  $effect(() => {
    if (!viewer.path) return;
    const url = new URL(location.href);
    url.searchParams.set("file", viewer.path);
    const fn = viewer.selected;
    const site = viewer.selection?.site;
    url.hash = fn && site !== null && site !== undefined ? `${fn.name}:${site}` : "";
    history.replaceState(null, "", url.toString());
  });

  /*
   * Stepping between claims also works from inside a field: Alt with the
   * arrows, or with j and k. The letters are matched by physical key, because
   * Option composes characters on macOS and would otherwise arrive as ∆ and ˚.
   */
  function onkeydown(event: KeyboardEvent) {
    if (!viewer.report) return;
    if (event.altKey && !event.metaKey && !event.ctrlKey) {
      const by =
        event.key === "ArrowDown" || event.code === "KeyJ"
          ? 1
          : event.key === "ArrowUp" || event.code === "KeyK"
            ? -1
            : 0;
      if (by) {
        event.preventDefault();
        viewer.step(by as 1 | -1);
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
      j: () => viewer.step(1),
      ArrowDown: () => viewer.step(1),
      k: () => viewer.step(-1),
      ArrowUp: () => viewer.step(-1),
      "]": () => viewer.stepFunction(1),
      "[": () => viewer.stepFunction(-1),
      Escape: () => viewer.selection && viewer.select(viewer.selection.functionId),
    };
    const move = moves[event.key];
    if (move) {
      event.preventDefault();
      move();
    }
  }

  const name = $derived(viewer.path.split("/").pop() ?? "");
</script>

<svelte:window {onkeydown} />

<div class="app">
  <header class="bar">
    <!-- The catalogue is a view, not a menu: what can be read is laid out to
         be read, and this returns to it. -->
    <button
      class="plain"
      aria-pressed={viewer.browsing}
      onclick={() => (viewer.browsing = !viewer.browsing)}
      disabled={viewer.busy || (!viewer.report && !viewer.browsing)}
      >{viewer.browsing && viewer.report ? "back to the report" : "browse sources"}</button
    >

    <OpenPath busy={viewer.busy} onopen={choose} />

    <!-- What the source view draws beyond the claims themselves. Both are off
         by default: they answer questions about the run, not about
         what it claims. -->
    <label class="tick">
      <input type="checkbox" bind:checked={viewer.showTypeScriptErrors} />
      TypeScript errors
    </label>
    <label class="tick">
      <input type="checkbox" bind:checked={viewer.showUnsupported} />
      undecoded bindings
    </label>

    <span class="path" title={viewer.path}>{name}</span>

    <span class="spacer"></span>

    {#if viewer.busy}
      <span class="note">collecting…</span>
    {:else if viewer.collection}
      <span class="note">
        {Math.round(
          viewer.collection.durationMs,
        )}ms
        {#if !viewer.collection.verified}· not checked{/if}
      </span>
    {/if}
    {#if !viewer.hasVerifier}
      <span class="warn">no verifier built — nothing can be checked</span>
    {/if}
  </header>

  {#if viewer.report?.outcome && !viewer.browsing}
    <!-- What the pipeline decided about this file, in its own words: the
         report viewer shows it and never reaches one of its own. -->
    {@const outcome = viewer.report.outcome}
    <p class="outcome" role="status">
      <strong>Pipeline: {outcome.status}</strong>
      at {outcome.phase}
      {#if outcome.status === "verified"}
        · {outcome.functions.join(", ")}
      {:else}
        · {outcome.detail}
      {/if}
    </p>
  {/if}

  {#if viewer.showTypeScriptErrors && !viewer.browsing}
    <section class="typescript-errors" aria-label="TypeScript errors">
      <strong>TypeScript errors</strong>
      {#if viewer.report?.diagnostics?.trim()}
        <pre>{viewer.report.diagnostics}</pre>
      {:else}
        <p>TypeScript reported no errors in this source.</p>
      {/if}
    </section>
  {/if}

  {#if viewer.error}
    <p class="error" role="status">{viewer.error}</p>
  {/if}

  {#if viewer.browsing}
    <Catalogue
      groups={viewer.groups}
      busy={viewer.busy}
      current={viewer.path}
      onopen={choose}
    />
  {:else if viewer.report && viewer.selected}
    {@const report = viewer.report}
    {@const fn = viewer.selected}
    <div class="body">
      <FunctionList
        functions={viewer.functions}
        collection={viewer.collection}
        selectedId={fn.id}
        onselect={(id) => viewer.select(id)}
      />
      <div class="centre">
        <div class="scroll">
          <SourceView
            {report}
            {fn}
            selected={viewer.selection?.site ?? null}
            unsupported={viewer.showUnsupported}
            typescriptErrors={viewer.showTypeScriptErrors}
            onselect={(site) => viewer.select(fn.id, site)}
          />
        </div>
        <div class="dock">
          <Selection
            {report}
            {fn}
            site={viewer.selection?.site ?? null}
          />
          <Obligation
            {fn}
            onselect={(offset) => viewer.selectAt(fn, offset)}
          />
          <Provenance bundle={viewer.bundle} collection={viewer.collection} />
        </div>
        <div class="rest"></div>
      </div>
    </div>
  {:else if !viewer.busy && !viewer.error}
    <p class="empty">Choose a source to collect and check its claims.</p>
  {/if}
</div>

<style>
  .outcome {
    margin: 0;
    padding: 6px 16px;
    border-bottom: 1px solid var(--rule);
    white-space: pre-wrap;
    overflow-wrap: anywhere;
    flex-shrink: 0;
  }
  .typescript-errors {
    padding: 10px 16px;
    border-bottom: 1px solid var(--rule);
    background: var(--panel);
    max-height: 25vh;
    overflow: auto;
    flex-shrink: 0;
  }
  .typescript-errors pre {
    white-space: pre-wrap;
    overflow-wrap: anywhere;
    margin: 6px 0 0;
  }
  .typescript-errors p {
    margin: 6px 0 0;
  }
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
    flex-wrap: wrap;
    gap: 8px 10px;
    padding: 8px 14px;
    border-bottom: 1px solid var(--rule);
    background: var(--panel);
    flex: none;
  }
  .path {
    font-family: ui-monospace, SFMono-Regular, Menlo, monospace;
    color: var(--faint);
    white-space: nowrap;
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
    white-space: nowrap;
  }
  .warn {
    color: var(--warn);
  }
  .plain {
    white-space: nowrap;
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
  .body {
    display: grid;
    grid-template-columns: minmax(180px, 16rem) 1fr;
    min-height: 0;
    flex: 1;
  }
  .centre {
    display: grid;
    /* The source takes the height it needs and the dock follows it, so a short
       function does not leave a field of nothing between the code and what is
       said about it. The last row absorbs the rest. */
    grid-template-rows: minmax(0, auto) auto 1fr;
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
  /* Absorbs whatever the source and the dock do not use. */
  .rest {
    min-height: 0;
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
