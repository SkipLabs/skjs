<script lang="ts">
  /*
   * Where what is on screen came from.
   *
   * Collapsed, because it answers a question you only sometimes have. It
   * records the run: which producer, what command, how long, and whether the
   * independent consumer was run at all — a report read from a file records no
   * such run and says so rather than implying one.
   */
  import type { Bundle, CollectionRun } from "../../types.ts";

  let {
    bundle,
    collection,
  }: {
    bundle: Bundle | null;
    collection: CollectionRun | null;
  } = $props();

  const m = $derived(bundle?.manifest);

  /** Fingerprints identify the exact inputs; they establish nothing by themselves. */
  const prints = $derived(
    m
      ? ([
          ["source", m.source?.sha256],
          ["claims", m.claimsSha256],
          ["verifier", m.verifierSha256],
          ["parser", m.parserSha256],
        ].filter(([, v]) => v) as [string, string][])
      : [],
  );
</script>

{#if collection || m}
  <details class="provenance">
    <summary>
      provenance
      {#if collection}
        <span class="line"
          >{collection.producer} · {collection.command} · {Math.round(
            collection.durationMs,
          )}ms · {collection.verified
            ? "checked by the verifier"
            : "not checked"}</span
        >
      {:else}
        <span class="line">read from a file; no run was recorded</span>
      {/if}
    </summary>

    <dl>
      {#if collection}
        <dt>ran at</dt>
        <dd>{new Date(collection.ranAt).toLocaleString()}</dd>
        <dt>producer ran</dt>
        <dd>{collection.producerRun ? "yes" : "no"}</dd>
      {/if}
      {#each prints as [what, value] (what)}
        <dt>{what} sha256</dt>
        <dd class="print">{value}</dd>
      {/each}
    </dl>

    {#if bundle?.manifest?.diagnostics}
      <details class="inner">
        <summary>producer diagnostics</summary>
        <pre>{bundle.manifest.diagnostics}</pre>
      </details>
    {/if}
  </details>
{/if}

<style>
  .provenance {
    border-top: 1px solid var(--rule);
    padding: 10px 16px 14px;
    background: var(--panel);
  }
  summary {
    cursor: pointer;
    color: var(--faint);
  }
  .line {
    font-family: ui-monospace, SFMono-Regular, Menlo, monospace;
    font-size: 11px;
    padding-left: 8px;
  }
  dl {
    display: grid;
    grid-template-columns: max-content 1fr;
    gap: 3px 14px;
    margin: 10px 0 0;
    font:
      11px/1.5 ui-monospace,
      SFMono-Regular,
      Menlo,
      monospace;
  }
  dt {
    color: var(--faint);
  }
  dd {
    margin: 0;
    color: var(--ink);
  }
  .print {
    word-break: break-all;
    color: var(--faint);
  }
  .inner {
    margin-top: 10px;
  }
  pre {
    margin: 6px 0 0;
    font:
      11px/1.5 ui-monospace,
      SFMono-Regular,
      Menlo,
      monospace;
    white-space: pre-wrap;
    color: var(--faint);
    max-height: 200px;
    overflow: auto;
  }
</style>
