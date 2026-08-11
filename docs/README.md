# The SKJS Soundness Corpus

A formal soundness model of the SKJS type checker, maintained as a small
corpus with a single source of truth for its open questions. Everything is
pinned to one revision of `main` (see [`shared/pin.tex`](shared/pin.tex)).

## Layout

| Path | Role |
|---|---|
| [`skjs-type-soundness.tex`](skjs-type-soundness.tex) | **Main paper**: the model, the theorems, and the rendered registry |
| [`ledger.yaml`](ledger.yaml) | **The registry**: the only place any assumption/obligation *status* is stated |
| [`deep-dives/`](deep-dives/README.md) | Eight evidence papers (A–H), each owning the proofs behind specific registry rows |
| [`deep-dives/issues/`](deep-dives/issues/) | Issue drafts (prose + fix directions); each executed witness is a runnable `repros/*.ts` file the draft references |
| [`generated/`](generated/) | Tables rendered from the registry (do not edit) |
| [`shared/`](shared/) | Preamble and revision pin shared by every document |
| [`tools/docs.py`](tools/docs.py) | Build and consistency tooling |

## Building and checking

```sh
python3 docs/tools/docs.py         # gen + check + build (default)
python3 docs/tools/docs.py check   # consistency checks only
python3 docs/tools/docs.py repro   # run each witness .ts at the pin, assert its verdict
```

`build` compiles every document (two `pdflatex` passes), keeps each `.pdf`
next to its `.tex`, and fails on errors or unresolved references;
auxiliary files live in the git-ignored `docs/.texbuild/`. `check`
enforces: registry integrity (status vocabulary, single owner, anchor
files exist), issue references resolve in both directions, no
temporal/history narration in any document, no numeric cross-document
references, cross-dive mentions backed by declared imports, and shared-pin
usage.

## Ownership

- The **main paper** owns the model's definitions and framework theorems.
- Each **registry row** has exactly one `owner` (a deep dive, or `main`
  for axioms the main paper states); other papers may `consume` a row —
  never another paper's internals. Any statement used across a paper
  boundary must be a registry row.
- **Witnesses** live in issue drafts; papers cite them by filename.
- **Implementation correspondence** is owned per claim by the paper making
  it (scoped by its `impl:` anchors) and corpus-wide by the tooling.

## Status semantics

Every registry row carries **exactly one status**, and statuses are
**local**: `proved` means the owning paper establishes the row *given the
residual rows its status note names* — it does **not** mean all transitive
assumptions are closed. The registry is a dependency graph, not a
certificate; corpus-level guarantees are always relative to the current
`assumed`/`open`/`violated` frontier. Where different facets of one
question have different grades, they are separate rows (e.g. `L-INTER`,
the proved containment, vs. `L-INTER-BOT`, the violated
bottom-implies-disjointness clause), so "treat the imported row as an
axiom" is never ambiguous.

## Review protocol

Correctness rests on three kinds of review with different scopes. In each
case the reviewer never needs another paper's proofs.

**Reviewing the main paper.** Scope: the paper plus the registry. Check
that (1) each proof is correct given the named assumptions — every
assumption is a registry row rendered in the Assumptions section, and the
paper's theorems depend on dive results only *as* registry statuses, never
on dive internals; (2) definitions and refinement rules are faithful to
the pinned implementation (the `impl:` anchors delimit what to read); (3)
the refinement master list matches the `evalCond` dispatch (manual until
the anchor cross-check lands).

**Reviewing a deep dive.** Scope: the dive, the main paper's
*definitions* (the shared language — always in scope by design), and the
dive's generated **Imports** table. Treat every imported row as an axiom;
check that (1) the proofs are correct given the imports, (2) each import
is cited with the registry's canonical statement, and (3) the dive's
implementation claims hold at the pin within its anchor scope. Findings
already verified by witness reproduction are marked as such.

**Reviewing an issue draft.** Run its referenced `repros/*.ts` (or
`docs.py repro` for all), and check the draft's runtime-on-Node and tsc
claims. Each repro's header states its expected `skjs check` verdict at
the pin; `docs.py repro` asserts it.

**Form of a review.** Reviews are read-only: report findings, change no
files. Severity is free-form (e.g. high/medium/low) — the finding
*category* above is what routes the fix, severity only orders it.

**What counts as a finding.** (a) A proof gap *given the imports as
axioms*; (b) an import cited with a meaning that differs from the
registry's canonical statement; (c) an implementation claim false at the
pin; (d) a registry-discipline violation (an undeclared cross-paper
dependency, a status stated outside the registry). Explicit
**non-findings**: a `proved` row with `open`/`assumed` residuals (that is
what local status means), and a consumed row whose *sibling facet row* is
violated when the proof uses only the row actually imported.

**Completeness claims get a wider net.** Anchors scope *faithfulness*
review (are the claims made true). When a paper claims **completeness**
of an inventory ("the complete state model", "every write site", "all
call sites"), reviewing that claim means adversarially searching the
source for members missing from the inventory — beyond the anchor list.
(This rule has already paid: an external review found the
`tenv.expandInter` mode flag missing from a state inventory; row
TENV-EXPANDINTER.)

**Why this composes.** Dives import only registry rows (enforced by
`check`), so the dependency graph is acyclic with depth one; per-paper
correctness relative to declared imports therefore gives corpus
correctness relative to the registry's statuses.

**Cadence.** Every change: `docs.py all`. After substantive edit waves
and on any pin bump: an adversarial referee pass (math-only) and a
code-vs-claim pass per affected paper, plus witness re-execution (until
the pinned tests land in `tests/`). On any status flip: walk the row's
`consumers` in the registry and revisit their conditional results.

## Cross-cutting observations

Three patterns span multiple papers (statuses: see the registry).

- **Cache entries recorded while candidate growth is suppressed** can become
  stale after growth resumes. Rows MR-1 and C-FREEZE-CACHE describe this
  problem for the subtyping and intersection caches; either version-key the
  entries or avoid recording them under `freezeCandidates`. Alias expansion
  does not read existing variable bindings, but its name-based key can collide
  across modules (row E-EXPKEY).
- **Unchecked refinement brands**: refinement trusts facts that subtyping does
  not validate. A callable can pass through `{}` into a type marked
  `CAbsent` (row F-CABSENT), and the array brand is never compared (row
  F-BRAND). Both require the checker to define and enforce when a brand may be
  introduced.
- **`⊥ ⟹ disjoint`** (row L-INTER-BOT) is consumed both by the main paper's
  refinement rules that discard impossible branches and by subtyping's
  covariant variable read (row O-GETCOV), so both uses must be reconsidered
  when it is repaired.

## Deferred by design

Expression soundness (row L-TC) and the full preservation theorem are the
capstone program, not series papers: every paper above is a prerequisite.
The model-to-implementation correspondence check is tooling (the anchor
cross-check of the main paper's Maintenance appendix), not a paper.
