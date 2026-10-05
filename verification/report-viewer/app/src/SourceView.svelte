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
  // ../../marks.mts decides what is drawn and how the marks pack onto rows, without a DOM.
  import {
    bracket,
    groupLines,
    lineAt,
    lineStarts,
    outcomeLabel,
    packRows,
    sourceMarks,
  } from "../../marks.mts";
  import type { Report, ShownFunction } from "../../model.mts";

  let {
    report,
    fn,
    selected,
    unsupported,
    typescriptErrors,
    onselect,
  }: {
    report: Report;
    fn: ShownFunction;
    /** The selected site's index, in source order. */
    selected: number | null;
    unsupported: boolean;
    typescriptErrors: boolean;
    onselect: (site: number) => void;
  } = $props();

  // Every claim, always. The old report viewer had a density switch; a claim that is
  // hidden is one you cannot tell is missing, and weight does the work the
  // switch was for.
  const drawn = $derived(
    sourceMarks(report, fn, { density: "all", unsupported, typescriptErrors }),
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
  /** The mark under a key, so a hover can light what it stands for. */
  const markAt = (key: string) =>
    [...drawn.entries, ...drawn.items].find((m) => m.id === key) ?? null;

  /** Which mark is hovered, and whether its failure symbol in particular is. */
  let hovered = $state<string | null>(null);
  let edgeHovered = $state<string | null>(null);

  /** The columns lit on each line, and which end of an edge each is. */
  type Lit = { from: number; to: number; end: string };

  const lit = $derived.by(() => {
    const covered = new Map<number, Lit[]>();
    const starts = lineStarts(report.source);
    const cover = (span: [number, number] | null, end = "") => {
      if (!span) return;
      for (let line = lineAt(starts, span[0]); ; line++) {
        const from = starts[line];
        if (from === undefined || from >= span[1]) break;
        const to = starts[line + 1] ?? report.source.length + 1;
        covered.set(line, [
          ...(covered.get(line) ?? []),
          {
            from: Math.max(span[0] - from, 0),
            to: Math.min(span[1], to - 1) - from,
            end,
          },
        ]);
        if (span[1] <= to) break;
      }
    };
    // Hovering the symbol of a failed edge obligation lights both of its ends:
    // one is the failure's own place, the other is where the edge comes from
    // or goes to, and the failure is about the pair.
    const edge = edgeHovered ? fn.failure?.edge : null;
    if (edge) {
      if (edge.from !== null) cover(fn.sites[edge.from]!.pos, "from");
      if (edge.to !== null) cover(fn.sites[edge.to]!.pos, "to");
      return covered;
    }
    const mark = hovered ? markAt(hovered) : null;
    if (mark) {
      // A producer diagnostic stands for no site, but the mark knows the
      // columns it covers on its own line.
      if (mark.site !== null) cover(fn.sites[mark.site]!.pos);
      else covered.set(mark.line, [{ from: mark.col, to: mark.end, end: "" }]);
    } else if (selected !== null) cover(fn.sites[selected]?.pos ?? null);
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
        {#each lit.get(line.index) ?? [] as at, i (i)}
          <span
            class="lit {at.end}"
            class:selected={!hovered && !edgeHovered}
            style="--from:{at.from}; --to:{at.to}"
          ></span>
        {/each}<span class="text">{line.text || " "}</span>
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
          class:selected={item.site !== null && item.site === selected}
          class:edge={edgeHovered !== null &&
            item.site !== null &&
            (item.site === fn.failure?.edge?.from ||
              item.site === fn.failure?.edge?.to)}
          style="--col:{item.col}"
          onclick={() => item.site !== null && onselect(item.site)}
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
          {#if item.mark}<span
              class="symbol"
              role="img"
              aria-label={outcomeLabel(item.mark)}
              onpointerenter={() => (edgeHovered = item.id)}
              onpointerleave={() => (edgeHovered = null)}>{item.mark}</span
            >{/if}
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
  /* A hovered failure lights its edge in the failure's own colour, so it is
     never mistaken for a hover or a selection. The two claims are told apart:
     where the edge comes from is underlined. */
  .lit.from,
  .lit.to {
    background: var(--bad-bg);
  }
  .lit.from {
    box-shadow: inset 0 -2px var(--bad);
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
  .mark.result .label {
    color: var(--accent);
    font-weight: 600;
  }
  .mark.entry .label {
    color: var(--faint);
  }
  /* TypeScript's own error about this span: what its checker said about the
     source. Neither a claim nor a verification result, so it
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
  .mark.edge .label {
    background: var(--bad-bg);
    color: var(--bad);
  }
</style>
