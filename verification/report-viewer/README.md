# Claim report reader

A source-centred inspector for producer claims and what the verifier made of
them. It is display-only: nothing it shows is proof evidence, and an outcome it
displays was reached by the verifier, never by the reader.

## Use

```sh
make viewer                                # builds and opens it
node verification/report-viewer/serve.mts  # http://localhost:8731, without opening
```

The producer selector chooses whose claims are read — **SKJS claims**,
**TypeScript claims** from `tools/tsc-claims.mts`, or **OCaml claims** from
[`ocaml-producer/`](../ocaml-producer/README.md). They answer for the same
sites and the same verifier adjudicates any of them, so switching re-reads the
open file through another one. Each implements its own fragment of the
language, and one that does not implement the open file says so in its own
words rather than showing a report with nothing in it: the OCaml producer needs
`dune build --root verification/ocaml-producer` to have been run, and refuses a
source it does not cover at the boundary that refuses it — the shared parser's
gate, or its own proposal.

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
diagnostics** puts its own errors under the spans they name, and **undecoded
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
the same keys steps from inside the editor, leaving the next claim ready to
type into. The letters match by physical key, since Option composes characters.

## Editing a claim

There is no workspace panel: a claim is edited at the claim. Selecting one
opens its editor holding the same surface syntax it is read in — `{ value:
boolean }`, `(boolean) => null`, `true | null`. The text is parsed on every
keystroke and applying is refused until it reads back into an encoding, so a
typo cannot be saved.

Reading back edits the claim it came from: what the surface names is replaced,
and what it cannot name — index signatures, call and construct shapes — is the
original's, never invented here. An encoding with no exact surface syntax is
edited as the producer's own JSON, which the editor switches to itself and says
why.

**Adding** a claim is different, and the difference is forced. There is no
original to resolve against, so the surface can only name what it says in full:
primitives and unions. An object or function type, and any environment, is
written as the encoding.

A candidate in the normalized encoding is edited the same way, in the same
editor. Its claims index the document's own type table, so a claim is shown
lifted into the syntax above and lowered back on apply, with any row the edit
needs interned into that table as the producer would have on first use. A claim
with no surface form there — an intersection of contracts, a type that refers
to itself — is edited as the encoding, as a list of labels.

A place the producer visited and claimed nothing at is selectable, and offers
the claim that belongs there. A function the candidate says nothing about asks
for its contract first, since every point claim is checked against it;
parameter names and their order come from the source. An attachment site is not
necessarily a required proof obligation.

Applying sends the candidate to the verifier against unchanged source; the
producer is not rerun. A refused candidate stays available for correction and
what was last displayed keeps saying what it said, because nothing unchecked is
shown as a result. A check that succeeds establishes that function's modeled
obligations; it does not make the producer's original claims true.

## Keeping a draft

A draft is meaningful for one file — its `sourceSha256` must match, and every
span is checked against the source it carries — so there is nothing to choose
and nothing to find. **Keep this draft** writes it beside the source, named
after it, the way the command-line tools already name what they write:

```
verification/tests/stateful-source/closures.ts
verification/tests/stateful-source/closures.candidate.json
```

Opening that source finds the draft, checks it, and shows what the verifier
made of it — a kept draft is a record of an edit, never a result. A draft about
a source that has since changed is stale and is not shown.

Keeping is explicit: applying an edit checks it and writes nothing, so
experiments leave no trace. The file is tracked, so a repair is something that
can be reviewed and kept. **Restore the producer's claims** puts them back and
discards the draft, because leaving it would resurrect it on the next open.

What is written is the candidate itself, so the same file is what the
command-line tool reads:

```sh
node verification/tools/annotate-source.mts closures.ts \
  --claims closures.candidate.json --verify verification/lean/.lake/build/bin/verifier
```

It names its own format and the source it is about, so `--format` is not needed
and a draft about a different file, or the same one before it changed, is
refused.

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
end and exercised by `tests/report-viewer.mts` without a browser:

- `model.mts` — what a bundle means, as the reader displays it: for each
  function, its sites in source order — an expression claim, an environment, or
  a place with nothing claimed — and its one failure, with the site it attached
  to.
- `marks.mts` — what the source view draws: which claims at what position, the
  outcome symbols, how marks pack onto rows without overlapping.
- `../tools/diagnostic-view.mts` — builds a typed obligation presentation when the report is generated; the panel renders it.
- `candidate.mts` — immutable candidate edits. Candidate inputs and stored
  results are never trusted proof evidence.
- `../tools/claim-text.mts` — claim types in surface syntax, printed and read
  back, and the lift and lowering between the normalized encoding and the
  structural one the surface reads. `report-viewer.mts` checks that printing
  and reading back returns the same encoding for every shape, and
  `annotated-source.mts` checks it over every claim in a real export.
- `serve.mts` — runs the producer and the report writer, and writes drafts. A
  producer is one collector here — SKJS in its container, `tsc-claims.mts`, or
  the shared parser feeding `producer.exe` — each ending at the same
  `annotate-source.mts --format source-claims --verify`, and a producer the
  address bar names but this list does not is read as the default rather than
  as something to run. It
  binds to loopback, runs one collection at a time, applies a 120-second
  timeout to each subprocess, rejects source changes detected during
  collection, and cleans temporary reports up either way. `SKJS_REPO`,
  `SKJS_BIN`, `SKJS_IMAGE` and `PORT` configure the local runner.

Function `pos` ranges in manifests use the same original UTF-16 offsets as
expression claims.

## The catalogue

A dropdown of ninety-eight basenames answers "which one was it called", which
is a question about a file already seen. The catalogue answers the other one.
Every group is visible at once, so nothing has to be remembered to be found,
and a file is never hidden behind a control — the same reason the source view
draws every claim.

A group says what it is, because a label states an outcome and a heading read
as a promise is worse than no heading: **SKJS unsound** carries "findings about
SKJS, kept as they are — do not make one verify", and **Unsupported examples**
carries "listing one never implies it verifies". **Current verifier examples**
is tested by the same source suites as `make verify`; **Claim repair** is the
deliberately rejected partial-collection exercise; the two **OCaml producer**
groups are that producer's own fixtures, its negative controls and named gaps
listed beside its verified ones.

A file says what it demonstrates where that is known — `callbacks.ts ·
higher-order calls / variance / capture`. Those come from the `area` field of
`ocaml-producer/cases.mts`, the inventory that already decides what each case
must do; writing them again here would be a second opinion about the same
fixture. Thirty-four of the ninety-eight have one. The rest are not described,
because an invented description is a claim about a fixture nobody checked, and
the gap is left visible rather than filled in.

The groups come from `examples.mts`, re-read for each page load, so adding an
example needs no restart. It exports two lists, because they answer different
questions: `groups` is corpus policy, which `verification/examples.mts` runs
SKJS and tsc over and holds to `expectedVerified`, reading its `files` as
paths; `viewerGroups` is what the reader lists, carrying the notes and
descriptions and reaching another producer's fixtures. `ExampleGroup` in
`types.ts` declares that shape for both the server and the page.

`Catalogue.svelte` scrolls at its wrapper and flows its columns inside, which
is load-bearing: flowing columns given a fixed height make further columns off
to the side instead of balancing, and a container that scrolls only downwards
then clips them — which hid two whole groups while this was being built.

## Source editing direction (not implemented)

Source editing should use an editor document with decorations, not embedded
report comments. Decorations can move with edits while remaining visibly stale.
Changed or ambiguous attachments must be invalidated. Initially any source edit
should invalidate the file's verification result; finer dependency tracking can
follow. During syntax errors, retain only unambiguous stale decorations. Accept
asynchronous results only for the exact source revision and candidate revision
analysed.

Report ids identify records within one snapshot. They are not stable identities
across edits; reattachment requires syntax and binding identity as well as
offset mapping. Moving an annotation is not evidence that its claim remains
valid.

Both producer collection paths supply `source-claims` candidates. Rigid parameters
use the same function-scoped references, and unavailable claims retain their sites.
SKJS native JSON is an import artifact, retained in provenance; editing and checking
new collections use the shared format. Sources outside the modeled fragment still
have an inspectable normalized report, with verification unavailable.
