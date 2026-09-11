<script lang="ts">
  /*
   * Editing a claim, where it is.
   *
   * There is no workspace panel: a claim is edited at the claim. The text is
   * the same surface syntax it is read in, parsed on every keystroke, and
   * applying is refused until it reads back into an encoding — so a typo cannot
   * be saved. Reading it back edits the claim it came from: what the surface
   * names is replaced, and what it cannot name — index signatures, call and
   * construct shapes — is the original's, never invented here.
   *
   * An encoding this reader cannot print exactly is edited as the producer's
   * own JSON instead, which is honest about what is being changed.
   */
  import surface from "../../../tools/claim-types.js";
  import { claimValue, type ClaimSite } from "../../candidate.js";
  import type { ShownFunction } from "../../model.js";
  import type { Candidate } from "../../types.ts";

  let {
    candidate,
    fn,
    site,
    busy,
    onapply,
  }: {
    candidate: Candidate;
    fn: ShownFunction;
    site: ClaimSite;
    busy: boolean;
    onapply: (value: unknown) => void;
  } = $props();

  /** The producer's own value here, which reading back is resolved against. */
  const current = $derived.by(() => {
    try {
      return claimValue(candidate, fn, site);
    } catch {
      return undefined;
    }
  });

  /** Surface text where it round-trips exactly; otherwise the raw encoding. */
  const printed = $derived(
    current === undefined
      ? null
      : surface.printClaimValue(site.kind, current),
  );
  const asJson = $derived(printed === null);

  let text = $state("");
  let touched = $state(false);

  // Selecting another claim abandons an unapplied edit rather than carrying it
  // somewhere it does not belong.
  $effect(() => {
    site;
    candidate;
    text = printed ?? JSON.stringify(current ?? null, null, 2);
    touched = false;
  });

  /** What the text reads back as, or why it does not read back at all. */
  const parsed = $derived.by(() => {
    if (current === undefined) return { error: "no claim here to edit" };
    try {
      return {
        value: asJson
          ? JSON.parse(text)
          : surface.readClaimValue(site.kind, text, current),
      };
    } catch (e) {
      return { error: (e as Error).message };
    }
  });

  const changed = $derived(
    touched && JSON.stringify(parsed.value) !== JSON.stringify(current),
  );

  function apply() {
    if ("value" in parsed && changed && !busy) onapply(parsed.value);
  }
</script>

<form
  class="editor"
  onsubmit={(e) => {
    e.preventDefault();
    apply();
  }}
>
  <label>
    <span>{asJson ? "edit as the producer's encoding" : "claim"}</span>
    {#if asJson}
      <textarea
        bind:value={text}
        oninput={() => (touched = true)}
        onkeydown={(e) => {
          // Enter makes a newline in a textarea, so applying takes the modifier.
          if (e.key === "Enter" && (e.metaKey || e.ctrlKey)) apply();
        }}
        rows="6"
        spellcheck="false"
      ></textarea>
    {:else}
      <input
        type="text"
        bind:value={text}
        oninput={() => (touched = true)}
        spellcheck="false"
      />
    {/if}
  </label>

  <div class="row">
    <button type="submit" disabled={!changed || !("value" in parsed) || busy}>
      {busy ? "checking…" : "apply and check"}
    </button>
    {#if touched && parsed.error}
      <span class="bad">{parsed.error}</span>
    {:else if changed}
      <span class="faint">checks against unchanged source; the producer is not rerun</span>
    {/if}
  </div>
</form>

<style>
  .editor {
    margin: 0 0 12px;
  }
  label span {
    display: block;
    color: var(--faint);
    margin-bottom: 4px;
  }
  input,
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
  input:focus,
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
