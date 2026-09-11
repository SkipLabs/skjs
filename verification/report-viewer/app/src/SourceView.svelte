<script lang="ts">
  /*
   * The source, with its claims drawn where they belong.
   *
   * A claim is not an annotation beside the code — it is what the producer says
   * about a span of it — so the marks sit under their spans, bracketed to the
   * exact columns, and clicking one selects it. What is drawn, and how the
   * marks pack onto rows without overlapping, is decided by `marks.js` without
   * a DOM, which is why the suites can check it.
   */
  import {
    bracket,
    groupLines,
    lineAt,
    lineStarts,
    packRows,
    sourceMarks,
  } from "../../marks.mts";
  import type { Report, ShownFunction } from "../../model.mts";

  let {
    report,
    fn,
    selectedMark,
    unsupported,
    producerErrors,
    onselect,
  }: {
    report: Report;
    fn: ShownFunction;
    selectedMark: string | null;
    unsupported: boolean;
    producerErrors: boolean;
    onselect: (markId: string) => void;
  } = $props();

  // Every claim, always. The old reader had a density switch; a claim that is
  // hidden is one you cannot tell is missing, and weight does the work the
  // switch was for.
  const drawn = $derived(
    sourceMarks(report, fn, { density: "all", unsupported, producerErrors }),
  );

  /** Every mark, grouped by the line it sits under and packed into rows. */
  const rowsByLine = $derived.by(() => {
    const grouped = groupLines([...drawn.entries, ...drawn.items]);
    return new Map(
      [...grouped].map(([line, items]) => [line, packRows(items)]),
    );
  });

  /** The function's own lines, numbered as they are in the file. */
  const lines = $derived.by(() => {
    const starts = lineStarts(report.source);
    const first = lineAt(starts, fn.pos[0]);
    const last = lineAt(starts, fn.pos[1] - 1);
    const text = report.source.split("\n");
    return Array.from({ length: last - first + 1 }, (_, i) => ({
      number: first + i + 1,
      text: text[first + i] ?? "",
      index: first + i,
    }));
  });
</script>

<div class="source">
  {#each lines as line (line.index)}
    <div class="row">
      <span class="gutter">{line.number}</span>
      <code class="code">{line.text || " "}</code>
    </div>
    {#each rowsByLine.get(line.index) ?? [] as packed, depth (depth)}
      <div class="row marks">
        <span class="gutter"></span>
        <span class="code">
          {#each packed.items as item (item.id)}
            <button
              class="mark {item.cls}"
              class:selected={item.id === selectedMark}
              style="--col:{item.col}"
              onclick={() => onselect(item.id)}
              title={item.label}
            >
              <span class="bracket"
                >{bracket(Math.max(1, item.end - item.col))}</span
              >
              <span class="label">{item.label}</span>
              {#if item.tag}<span class="tag">{item.tag}</span>{/if}
              {#if item.mark}<span class="symbol">{item.mark}</span>{/if}
            </button>
          {/each}
        </span>
      </div>
    {/each}
  {/each}
</div>

<style>
  .source {
    font:
      12px/1.5 ui-monospace,
      SFMono-Regular,
      Menlo,
      monospace;
    padding: 10px 0 24px;
    min-width: max-content;
  }
  .row {
    display: flex;
    align-items: baseline;
    gap: 12px;
    padding: 0 16px;
  }
  .gutter {
    flex: 0 0 3ch;
    text-align: right;
    color: var(--faint);
    user-select: none;
  }
  .code {
    white-space: pre;
    color: var(--ink);
    position: relative;
    display: block;
  }
  .marks .code {
    height: 1.5em;
  }
  /* Marks sit in the same monospace grid as the code above them, so a column
     here is the column of the character it is about. */
  .mark {
    position: absolute;
    left: calc(var(--col) * 1ch);
    display: inline-flex;
    align-items: baseline;
    gap: 0.5ch;
    font: inherit;
    white-space: pre;
    color: var(--claim);
    background: none;
    border: 0;
    border-radius: 3px;
    padding: 0;
    cursor: pointer;
  }
  .mark:hover .label {
    background: var(--claim-bg);
  }
  .mark.selected .label {
    background: var(--accent-bg);
    color: var(--accent);
  }
  .bracket {
    color: var(--claim-edge);
  }
  .label {
    border-radius: 3px;
    padding: 0 0.25ch;
  }
  /* A failed claim is still a claim: it carries a symbol; it is not drawn as a
     different kind of thing. */
  .mark.failed .symbol {
    color: var(--bad);
    font-weight: 600;
  }
  .mark.entry .label {
    color: var(--faint);
  }
  .mark.gap {
    color: var(--faint);
  }
  .mark.gap .bracket {
    color: var(--rule);
  }
  .tag {
    color: var(--faint);
  }
</style>
