# Skip Code Notes (Living Log)

A living collection of lessons about writing good **Skip** code in this repo,
contributed by agent sessions (this one and others). It complements
[writing-code.md](writing-code.md): that file holds the stable rules; this file
accumulates the specifics we learn by doing — `skargo` errors, test failures,
review feedback, and corrections from the project owner.

## How to Contribute

- **Read the latest entries before writing `.sk` code**, so recent lessons are
  fresh in mind.
- **Append an entry whenever you learn a new lesson — above all when the user
  tells you to do something differently.** If the user corrects your Skip code
  (style, pattern, naming, structure, anything), record the correction here in
  the same session, then apply it to the work in progress. Do not wait to be
  asked twice.
- **Newest entries first.** Keep each entry short: a `###` heading with the
  date and a short title, one or two sentences stating the rule, a source tag
  (`user correction`, `skargo error`, `test failure`, `review`), and a small
  before/after snippet when it helps.
- **Don't duplicate.** If your lesson extends an existing entry, edit that
  entry instead of adding a near-copy. If an entry proves durable and general,
  promote it into [writing-code.md](writing-code.md) and leave a pointer here.
- This file is for lessons about the `.sk` implementation language. Rules about
  the TypeScript subset SKJS accepts or rejects live in
  [skjs-rules.md](../skjs-rules.md) — do not record those here.

Example entry:

```markdown
### 2026-11-20 — Prefer `HashMap` over nested `Map` for two-key lookups

Source: user correction. When a lookup needs two keys, key a single `HashMap`
by a tuple instead of nesting `Map`s; nested maps force callers to unwrap two
optionals and read worse.

    // worse                          // better
    m.get(a)?.get(b)                 m.get([a, b])
```

## Log

<!-- Newest entries first. Add yours at the top of this section. -->

_No entries yet — add the first one the next time you learn something, especially
when the user corrects you._
