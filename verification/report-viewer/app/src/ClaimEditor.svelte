<script lang="ts">
  /*
   * Editing a claim, where it is.
   *
   * There is no workspace panel: a claim is edited at the claim. The text is
   * the same surface syntax it is read in, parsed on every keystroke, and
   * applying is refused until it reads back into an encoding — so a typo cannot
   * be saved. Reading back edits the claim it came from: what the surface names
   * is replaced, and what it cannot name — index signatures, call and construct
   * shapes — is the original's, never invented here.
   *
   * That is also why a claim being *added* is different. There is no original
   * to resolve against, so the surface can only name what it says in full:
   * primitives and unions. An object or function type, and any environment,
   * has to be written as the producer's own encoding — which the editor says
   * rather than letting the attempt fail obscurely.
   *
   * This is the one editor. A candidate in the normalized encoding reaches it
   * lifted into the encoding the surface reads, and is lowered back on apply.
   */
  import surface from "../../../tools/claim-text.mts";
  import type { ClaimSite } from "../../candidate.mts";

  let {
    kind,
    current,
    busy,
    onapply,
  }: {
    kind: ClaimSite["kind"];
    /** The claim being edited, or undefined where one is being added. */
    current: unknown | undefined;
    busy: boolean;
    onapply: (value: unknown) => void;
  } = $props();

  const adding = $derived(current === undefined);

  /** Surface text where the claim round-trips exactly; null where it does not. */
  const printed = $derived(
    adding ? null : surface.printClaimValue(kind, current),
  );

  /** Whether the encoding is being written directly, rather than the surface. */
  let raw = $state(false);
  let text = $state("");
  let touched = $state(false);

  // A different claim abandons an unapplied edit rather than carrying it
  // somewhere it does not belong.
  $effect(() => {
    kind;
    current;
    raw = !adding && printed === null;
    text = printed ?? (adding ? "" : JSON.stringify(current, null, 2));
    touched = false;
  });

  /** What the text reads back as, or why it does not read back at all. */
  const parsed = $derived.by((): { value?: unknown; error?: string } => {
    if (!text.trim()) return { error: "" };
    try {
      return {
        value: raw
          ? JSON.parse(text)
          : surface.readClaimValue(kind, text, current),
      };
    } catch (e) {
      return { error: (e as Error).message };
    }
  });

  const ready = $derived(
    "value" in parsed &&
      (adding || JSON.stringify(parsed.value) !== JSON.stringify(current)),
  );

  function apply() {
    if (ready && !busy) onapply(parsed.value);
  }
</script>

<form
  class="editor"
  onsubmit={(e) => {
    e.preventDefault();
    apply();
  }}
>
  <div class="head">
    <span class="what">
      {adding ? `add the ${kind} claim` : "claim"}
    </span>
    <label class="as-raw">
      <input
        type="checkbox"
        bind:checked={raw}
        disabled={!adding && printed === null}
      />
      write the encoding
    </label>
  </div>

  {#if raw}
    <textarea
      bind:value={text}
      oninput={() => (touched = true)}
      onkeydown={(e) => {
        // Enter makes a newline in a textarea, so applying takes the modifier.
        if (e.key === "Enter" && (e.metaKey || e.ctrlKey)) apply();
      }}
      rows="6"
      spellcheck="false"
      placeholder={kind === "environment"
        ? '[{ "name": "x", "type": { "top": false, "atoms": [] } }]'
        : '{ "top": false, "atoms": [] }'}
    ></textarea>
  {:else}
    <input
      type="text"
      bind:value={text}
      oninput={() => (touched = true)}
      spellcheck="false"
      placeholder={kind === "environment" ? "x: true, y: boolean" : "boolean"}
    />
  {/if}

  <div class="row">
    <button type="submit" disabled={!ready || busy}>
      {busy ? "checking…" : adding ? "add and check" : "apply and check"}
    </button>
    {#if touched && parsed.error}
      <span class="bad">{parsed.error}</span>
    {:else if !adding && printed === null && !raw}
      <span class="faint">this encoding has no exact surface syntax</span>
    {:else if ready}
      <span class="faint"
        >checks against unchanged source; the producer is not rerun</span
      >
    {/if}
  </div>
</form>

<style>
  .editor {
    margin: 0 0 12px;
  }
  .head {
    display: flex;
    align-items: baseline;
    justify-content: space-between;
    gap: 12px;
    margin-bottom: 4px;
  }
  .what {
    color: var(--faint);
  }
  .as-raw {
    color: var(--faint);
    display: inline-flex;
    align-items: center;
    gap: 5px;
  }
  input[type="text"],
  textarea {
    width: 100%;
    font:
      12px/1.5 ui-monospace,
      SFMono-Regular,
      Menlo,
      monospace;
    padding: 6px 8px;
    border: 1px solid var(--rule);
    border-radius: 5px;
    background: var(--field);
    color: var(--ink);
    resize: vertical;
  }
  input[type="text"]:focus,
  textarea:focus {
    outline: 2px solid var(--accent);
    outline-offset: -1px;
  }
  .row {
    display: flex;
    align-items: center;
    gap: 10px;
    margin-top: 6px;
  }
  button {
    font: inherit;
    padding: 4px 12px;
    border: 1px solid var(--rule);
    border-radius: 5px;
    background: var(--field);
    color: var(--ink);
    cursor: pointer;
  }
  button:disabled {
    color: var(--faint);
    cursor: default;
  }
  .bad {
    color: var(--bad);
  }
  .faint {
    color: var(--faint);
  }
</style>
