<script lang="ts">
  /*
   * The source, with its claims drawn where they belong.
   *
   * A claim is not an annotation beside the code — it is what the producer says
   * about a span of it — so the marks sit under their spans, bracketed to the
   * exact columns, and clicking one selects it. An entry claim is what holds
   * before its statement runs, so that one sits above. What is drawn, and how
   * the marks pack onto rows without overlapping, is decided by `marks.mts`
   * without a DOM, which is why the suites can check it.
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

  /** Marks grouped by line and packed into rows. */
  const packed = (marks: typeof drawn.items) =>
    new Map([...groupLines(marks)].map(([line, on]) => [line, packRows(on)]));
  /*
   * An entry claim is the environment on entry to its statement — what holds
   * before it runs — so it sits above the line. Everything else is about a
   * span of the line and sits under it.
   */
  const above = $derived(packed(drawn.entries));
  const below = $derived(packed(drawn.items));

  /**
   * The source a mark is about. A mark's own `col`/`end` stop at the end of its
   * line, which is right for the bracket it draws; the span itself can cross
   * several lines, and that is what the code should light up.
   */
  function spanOf(id: string): [number, number] | null {
    const index = Number(id.slice(1));
    if (!Number.isInteger(index)) return null;
    const list =
      id[0] === "e"
        ? fn.exprs
        : id[0] === "n"
          ? fn.entries
          : id[0] === "g"
            ? fn.gaps
            : id[0] === "m"
              ? (fn.missingSites ?? [])
              : [];
    return (list[index] as { pos?: [number, number] })?.pos ?? null;
  }

  /** Which line is hovered, and the columns the claim covers on it. */
  let hovered = $state<string | null>(null);

  const lit = $derived.by(() => {
    const id = hovered ?? selectedMark ?? "";
    const covered = new Map<number, [number, number]>();
    const span = spanOf(id);
    if (!span) {
      // A producer diagnostic is not a claim and has no entry in those lists,
      // but the mark already knows the columns it covers on its own line.
      const mark = [...drawn.entries, ...drawn.items].find((m) => m.id === id);
      if (mark) covered.set(mark.line, [mark.col, mark.end]);
      return covered;
    }
    const starts = lineStarts(report.source);
    for (let line = lineAt(starts, span[0]); ; line++) {
      const from = starts[line];
      if (from === undefined || from >= span[1]) break;
      const to = starts[line + 1] ?? report.source.length + 1;
      covered.set(line, [
        Math.max(span[0] - from, 0),
        Math.min(span[1], to - 1) - from,
      ]);
      if (span[1] <= to) break;
    }
    return covered;
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
    {#each above.get(line.index) ?? [] as packed, depth (depth)}
      {@render marks(packed.items, "╷")}
    {/each}
    <div class="row">
      <span class="gutter">{line.number}</span>
      <code class="code">
        {#if lit.has(line.index)}
          {@const [from, to] = lit.get(line.index)!}
          <span
            class="lit"
            class:selected={!hovered}
            style="--from:{from}; --to:{to}"
          ></span>
        {/if}<span class="text">{line.text || " "}</span>
      </code>
    </div>
    {#each below.get(line.index) ?? [] as packed, depth (depth)}
      {@render marks(packed.items, null)}
    {/each}
  {/each}
</div>

<!-- One packed row of marks. An entry's tick points down at the statement it
     is the entry to; every other bracket spans what it is about. -->
{#snippet marks(items: typeof drawn.items, tick: string | null)}
  <div class="row marks">
    <span class="gutter"></span>
    <span class="code">
      {#each items as item (item.id)}
        <button
          class="mark {item.cls}"
          class:selected={item.id === selectedMark}
          style="--col:{item.col}"
          onclick={() => onselect(item.id)}
          onpointerenter={() => (hovered = item.id)}
          onpointerleave={() => (hovered = null)}
          onfocus={() => (hovered = item.id)}
          onblur={() => (hovered = null)}
          title={item.label}
        >
          <span class="bracket"
            >{tick ?? bracket(Math.max(1, item.end - item.col))}</span
          >
          <span class="label">{item.label}</span>
          {#if item.tag}<span class="tag">{item.tag}</span>{/if}
          {#if item.mark}<span class="symbol">{item.mark}</span>{/if}
        </button>
      {/each}
    </span>
  </div>
{/snippet}

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
  /* The source a claim is about, lit behind the text in the same monospace
     grid the marks sit in. Hovering a mark lights its span; with nothing
     hovered, the selected claim keeps its own lit, more faintly. */
  .lit {
    position: absolute;
    left: calc(var(--from) * 1ch);
    width: calc((var(--to) - var(--from)) * 1ch);
    top: 0;
    bottom: 0;
    border-radius: 2px;
    background: var(--claim-bg);
  }
  .lit.selected {
    background: var(--accent-bg);
  }
  .text {
    position: relative;
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
  /* The producer's own diagnostic about this span: what its checker said while
     running over the source. Neither a claim nor a verification result, so it
     reads as neither — its own colour, and a dotted bracket so it is still
     distinguishable where colour is not. */
  .mark.err {
    color: var(--diag);
  }
  .mark.err .bracket {
    color: var(--diag-edge);
  }
  .mark.err:hover .label,
  .mark.err.selected .label {
    background: var(--diag-bg);
    color: var(--diag);
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
