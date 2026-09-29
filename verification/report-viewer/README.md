# Claim report reader

A source-centred inspector for producer claims and what the verifier made of
them. It is display-only: nothing it shows is proof evidence, and an outcome it
displays was reached by the verifier, never by the reader.

## Use

```sh
make viewer                                # builds and opens it
node verification/report-viewer/serve.mts  # http://localhost:8731, without opening
```

The producer selector chooses whose claims are read — **OCaml claims** from
[`ocaml-producer/`](../ocaml-producer/README.md), the default, or **TypeScript
claims** from `tools/tsc-claims.mts`. They answer for the same
sites and the same verifier adjudicates any of them, so switching re-reads the
open file through another one. Each implements its own fragment of the
language, and one that does not implement the open file says so in its own
words rather than showing a report with nothing in it. The OCaml claims are
one run of the pipeline, `ocaml-producer/check.mts` — the run its suites judge,
so any file it runs opens here, with no setup of its own — and the page is
built from that run's artifacts. Its outcome is the line under the bar. A
source it refuses before any claim is proposed — at the shared parser's gate,
or at the producer's proposal — is shown whole under that outcome, and with
**producer diagnostics** ticked, the TypeScript errors the gate read are drawn
under the spans TypeScript gives them. It needs
`dune build --root verification/ocaml-producer` to have been run.

Opening the reader without a file in the link shows the **catalogue** — every
source it offers, laid out to be read — and **browse sources** returns to it.
Or type any repository-relative path into **Open any repository path…**; it
suggests matching `.ts` sources as you type, and a full path works whether or
not it is listed. Paths outside the repository are refused. The producer runs
on every open — nothing is cached — and the verifier checks what it produced,
so nothing is displayed as a result without having been checked.

The address bar follows the view: `?file=…&producer=…#function:site`. Reopening
that link restores it. A site is named by its function and its index in source
order, because names survive a recollection and positional ids do not; a link
into a report that has changed resolves by name or is dropped, rather than
quietly selecting something else.

## What is on screen

**The functions**, down the left, each with the two outcomes that matter:
`✓→✓` is the producer's own verdict on the program, then what proof search
found over the claims it made. They are different questions. `✗` on the right
means no derivation was found — never that a claim is false. `?` means checking
could not properly be attempted: a claim it needed is missing, or the source is
outside the fragment. A disagreement is amber.

**The source**, with the function's claimed result drawn at its annotation as
`returns T` — every return is checked against it, so it reads differently from
a claim — and each claim bracketed under the span it is about — except
an entry's environment, which is what holds before its statement runs and so
sits above it. Every
claim is drawn; there is no density switch, because a claim that is hidden is
one you cannot tell is missing. Weight does that work instead: an entry's
environment reads faintly, a failed claim carries its symbol, and a place the
producer never visited is dashed.

Two ticks change what else is drawn, both off by default because they answer
questions about the producer's run rather than about what it claims: **producer
diagnostics** opens the recorded messages and puts located errors under the
spans they name. An empty report explicitly says no diagnostics were recorded;
messages without a usable source span remain visible in the panel. TS checker
messages travel with its claims. **Undecoded
bindings** shows the bindings whose types it could not state.

**The selected claim**, docked beneath the source rather than in a rail away
from it: its span, its type in surface syntax, the producer's own encoding, and
— where one is there — the claim's failure.

**Why verification stopped**, where the verifier emitted a structured
obligation diagnostic: what it had and what had to follow from it, the bindings
that differ marked, and both ends of an edge selectable — hovering the `✗`
lights the other claim of the edge and both spans, the origin underlined. A
failed return contract is an edge too, from the returned expression to the
result. The role comes from
the record rather than from the span — a return contract and the returned
expression's own claim share a span and are different obligations — and where
the record names no specific role, the panel says nothing rather than inventing
one. See [OBLIGATION-DIAGNOSTICS](../OBLIGATION-DIAGNOSTICS.md).

**Provenance**, collapsed: the producer, the exact command, how long it took,
whether the independent consumer ran, and the fingerprints of the inputs.

Keyboard: <kbd>j</kbd>/<kbd>k</kbd> or the arrows step through the marks in
source order, <kbd>[</kbd>/<kbd>]</kbd> change function, <kbd>Esc</kbd> clears
the mark. Those are ignored while typing, so <kbd>⌥</kbd>/<kbd>Alt</kbd> with
the same keys steps from inside a field. The letters match by physical key,
since Option composes characters.

A place the producer visited and claimed nothing at is selectable too; an
attachment site is not necessarily a required proof obligation. A function the
producer says nothing about is listed with no claims.

## How it is built

`app/` is a Svelte 5 application in TypeScript, built by Vite:

```sh
npm --prefix verification/report-viewer/app run check   # types, templates included
npm --prefix verification/report-viewer/app run build   # dist/, which serve.mts serves
npm --prefix verification/report-viewer/app run dev     # vite, with hot reload
```

`npm run check` is `svelte-check`, and that distinction earns its place: `tsc`
does not look inside a component's template, which is exactly where a wrong
property name hides. It needs TypeScript 6 alongside 7 and the `--tsgo` flag,
its own transitional requirement; the trusted front end in `tools/` is
unaffected and builds against 7 alone.

The view is the only part that is Svelte. Everything it reasons with is a
module beside it, checked by `tools/tsconfig.json` like the rest of the front
end and exercised by the reader section of `ocaml-producer/test.mts` without a
browser:

- `model.mts` — what a bundle means, as the reader displays it: for each
  function, its sites in source order — an expression claim, an environment, or
  a place with nothing claimed — and its one failure, with the site it attached
  to.
- `marks.mts` — what the source view draws: which claims at what position, the
  outcome symbols, how marks pack onto rows without overlapping.
- `../tools/diagnostic-view.mts` — builds a typed obligation presentation when the report is generated; the panel renders it.
- `../tools/claim-text.mts` — claim types in surface syntax, and the lift from
  the normalized encoding into the structural one the surface prints.
- `serve.mts` — runs the producer and the report writer. A
  producer is one collector here — a `check.mts` run or `tsc-claims.mts` —
  each ending at the same
  `annotate-source.mts --format source-claims --verify` (for a `check.mts`
  run, over its Fragment and, where it verified, its evidence, with
  `--fragment` and `--evidence`), and a producer the
  address bar names but this list does not is read as the default rather than
  as something to run. It
  binds to loopback, runs one collection at a time, applies a 120-second
  timeout to each subprocess, rejects source changes detected during
  collection, and cleans temporary reports up either way. `SKJS_REPO` (the
  repository root) and `PORT` configure the local runner.

Function `pos` ranges in manifests use the same original UTF-16 offsets as
expression claims.

## The catalogue

A dropdown of ninety-eight basenames answers "which one was it called", which
is a question about a file already seen. The catalogue answers the other one.
Every group is visible at once, so nothing has to be remembered to be found,
and a file is never hidden behind a control — the same reason the source view
draws every claim.

A group says what it is, because a label states an outcome and a heading read
as a promise is worse than no heading: **Unsupported examples** carries
"listing one never implies it verifies". **Current verifier examples** are the
sources the corpus's tsc column checks; the two **OCaml producer** groups are that producer's own fixtures, its negative controls and named gaps
listed beside its verified ones.

A file always says what it demonstrates — `callbacks.ts ·
higher-order calls / variance / capture`. Those come from the `area` field of
`ocaml-producer/cases.mts`, the inventory that already decides what each case
must do; writing them again here would be a second opinion about the same
fixture. Other
examples pair their paths with descriptions in the catalogue. `GroupFile.about`
is required, and catalogue construction rejects empty or multiline text, even
when loaded by Node without type checking. The page renders it unconditionally.

The groups come from `examples.mts`, re-read for each page load, so adding an
example needs no restart. It exports two lists, because they answer different
questions: `groups` is the corpus, which `verification/examples.mts` runs the
tsc producer over, reading its `files` as paths; `viewerGroups` is what the reader lists, carrying the notes and
descriptions and reaching another producer's fixtures. `ExampleGroup` in
`types.ts` declares that shape for both the server and the page.

`Catalogue.svelte` scrolls at its wrapper and flows its columns inside, which
is load-bearing: flowing columns given a fixed height make further columns off
to the side instead of balancing, and a container that scrolls only downwards
then clips them — which hid two whole groups while this was being built.

## Report identity

Report ids identify records within one snapshot. They are not stable identities
across source changes; reattachment would need syntax and binding identity as
well as offset mapping.

Both producers supply `source-claims` documents. Rigid parameters use the same
function-scoped references, and unavailable claims retain their sites. Sources
outside the modeled fragment still have an inspectable normalized report, with
verification unavailable.
