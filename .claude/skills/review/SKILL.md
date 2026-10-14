---
name: review
description: Commit records and review pages for verification work. Use when committing verification changes, when an agent reports its work, and when the user asks to review, compare or choose branches to merge. Every commit message is a structured record; review pages are rendered from records, never written by hand.
---

# Commit records and review pages

Every commit on verification work carries a **record**: a commit message whose
body and trailers state what the change is, at the subject's own level. A
review page is rendered from records, for one commit or for whole branches.
Nothing about a change is written twice: an agent's final report quotes its
records; a pull request description is rendered from them.

## The record

```
<subject: present tense, what the code now does>

<optional prose paragraph>

Example:
    <indented source, at most 10 lines: the unit's essential code>

Rule:
    <indented rule in Unicode mathematics: ⟦…⟧ ≤ ⊓ ⊔ → ∀ ∃ ⊢; premises on one
    line, then the conclusion; name the rule in parentheses>

Why: <prose; for a refusal use "Principle:" and "Counterexample:" instead,
the counterexample as indented code followed by what Node prints>

Units: <tests/expect-error file.ts#unit …, space-separated>
Outcome: verified | refused | gap | no-behaviour-change
Parts: <from: lean-semantics lean-rules lean-proofs lean-lowering producer
 parser wire trust docs tests format>
Lean: <theorems and definitions, separated by "; ">
Wire: <the wire change>
Trust: <the new trust sentence, or none>
Depends: <branch or commit the units need beside this one>
Measured: <number, before -> after, and what produced it>
Tests: +positive-case -negative-case forged:what-was-forged
Co-Authored-By: <attribution>
```

- **Prose sections** are a line `Name:` followed by text or an indented
  (4 spaces) block. Any name may be used; `Example` renders as code and
  `Rule` as mathematics.
- **The final block is git trailers**: `Key: value` lines, continuation lines
  indented by one space, nothing else after them. `git interpret-trailers
  --parse` must read every key. Omit a key that does not apply, except
  `Outcome` and `Trust`, which every behaviour change states.
- **Mathematics is Unicode, never TeX**: commit messages are read raw in
  terminals and on GitHub. In a `Rule:` block, an inference rule is its
  premises (side by side, separated by three or more spaces), a line of `─`
  ending with the rule's name in parentheses, then its conclusion; a blank
  line separates it from other formulas. `_x`, `_{…}` and `^{…}` render as
  sub- and superscripts; an indented line continues the formula above.
- **Wording** follows the global writing rules: present facts, positive
  statements, claims as strong as their evidence, each number labelled by what
  produced it.
- A refusal record carries the counterexample that makes it principled; a gap
  says what is missing in `Why:`.

## Rendering

```sh
node verification/tools/commit-records.mts --out review.html <rev>...
node verification/tools/commit-records.mts --out review.html <base>..<branch>...
```

- A revision renders one card. A range renders its commits as cards under a
  branch heading, and the page opens with a table per branch (units by
  outcome, parts, new trust, wire, depends) and the files more than one branch
  changes.
- `--fragment` omits the document skeleton, for publishing with the Artifact
  tool. The page uses no script and no external data, so the same file works
  offline (its fonts fall back to system faces).
- A note on `refs/notes/records` overrides the commit message's record. Use
  it only for what is added after a commit exists (a review decision, a
  correction); the record itself belongs in the commit message.

## When to produce a review

- After a batch of agent work, before any merge: render each branch's range,
  publish it as an Artifact and give the user the link plus the offline file.
  The user chooses what to merge from it.
- When an agent finishes: its report lists the commits; their records are the
  description of the work.
- Agent briefs require records in commit messages (paste the format above
  into the brief).
