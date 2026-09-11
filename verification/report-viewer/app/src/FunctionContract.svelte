<script lang="ts">
  /*
   * The contract for a function the candidate says nothing about.
   *
   * Parameter names and their order come from the source, so only the types are
   * asked for; no offsets are entered and no type is inferred or defaulted.
   * Supplying it is what reveals that function's point-claim sites — none of
   * which are invented here either. Fresh verification checks the contract
   * against the source's own annotations.
   */
  import surface from "../../../tools/claim-types.mts";
  import type { ShownFunction } from "../../model.mts";

  let {
    fn,
    busy,
    onsubmit,
  }: {
    fn: ShownFunction;
    busy: boolean;
    onsubmit: (contract: {
      params: { name: string; type: unknown }[];
      result: unknown;
    }) => void;
  } = $props();

  const names = $derived(fn.parameters ?? []);
  let params = $state<string[]>([]);
  let result = $state("");

  $effect(() => {
    params = names.map(() => "");
    result = "";
  });

  /**
   * Read one field. There is no original to resolve against, so the surface
   * can only name what it says in full, and a shape it cannot name is written
   * as the producer's encoding.
   */
  function read(text: string): { value?: unknown; error?: string } {
    if (!text.trim()) return { error: "" };
    try {
      return { value: surface.readClaimValue("expression", text, undefined) };
    } catch (e) {
      try {
        return { value: JSON.parse(text) };
      } catch {
        return { error: (e as Error).message };
      }
    }
  }

  type Read = { value?: unknown; error?: string };
  const readParams = $derived<Read[]>(params.map(read));
  const readResult = $derived<Read>(read(result));
  const ready = $derived(
    readParams.every((p) => "value" in p) && "value" in readResult,
  );
  const firstError = $derived(
    [...readParams, readResult].find((p) => p.error)?.error ?? "",
  );

  function submit() {
    if (!ready || busy) return;
    onsubmit({
      params: names.map((name, i) => ({
        name,
        type: readParams[i]!.value,
      })),
      result: readResult.value,
    });
  }
</script>

<form
  class="contract"
  onsubmit={(e) => {
    e.preventDefault();
    submit();
  }}
>
  <p class="lead">
    Its parameters and their order come from the source; give each a type, and
    the result.
  </p>

  <div class="fields">
    {#each names as name, i (name)}
      <div class="field">
        <span>{name}</span>
        <input
          type="text"
          bind:value={params[i]}
          spellcheck="false"
          placeholder="boolean"
        />
      </div>
    {:else}
      <p class="faint">It takes no parameters.</p>
    {/each}
    <div class="field">
      <span>returns</span>
      <input
        type="text"
        bind:value={result}
        spellcheck="false"
        placeholder="null"
      />
    </div>
  </div>

  <div class="row">
    <button type="submit" disabled={!ready || busy}>
      {busy ? "checking…" : "add the contract and check"}
    </button>
    {#if firstError}
      <span class="bad">{firstError}</span>
    {/if}
  </div>
</form>

<style>
  .contract {
    margin: 0;
  }
  .lead {
    margin: 0 0 10px;
    max-width: 68ch;
    color: var(--faint);
  }
  .fields {
    display: grid;
    gap: 10px;
    max-width: 40rem;
  }
  .field {
    display: grid;
    grid-template-columns: 10ch 1fr;
    align-items: baseline;
    gap: 10px;
  }
  .field span {
    color: var(--faint);
    font-family: ui-monospace, SFMono-Regular, Menlo, monospace;
    text-align: right;
    overflow: hidden;
    text-overflow: ellipsis;
  }
  input {
    font:
      12px/1.5 ui-monospace,
      SFMono-Regular,
      Menlo,
      monospace;
    padding: 5px 8px;
    border: 1px solid var(--rule);
    border-radius: 5px;
    background: var(--field);
    color: var(--ink);
  }
  input:focus {
    outline: 2px solid var(--accent);
    outline-offset: -1px;
  }
  .row {
    display: flex;
    align-items: center;
    gap: 10px;
    margin-top: 10px;
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
    margin: 0;
    color: var(--faint);
  }
</style>
