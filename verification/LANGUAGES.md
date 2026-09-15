# The pipeline's languages

Data crosses this pipeline as a sequence of distinct representations, each with
its own syntax. This file names them, says who owns each one, and records the
convention their files follow. It exists because they had drifted into being
named five different ways, and a language whose file cannot be found is a
language whose cases get missed: the omissions that prompted this list were
found by writing it, not by a test.

## The convention

1. **One language, one name.** One file per language per side.
2. **A Lean module and its TypeScript mirror share that name**, `PascalCase.lean`
   against `kebab-case.mts`.
3. **A file that defines a language is named for it. A file that consumes one is
   `<language>-<role>`** — `fragment-parse`, `claim-text`, `diagnostic-view`.
4. **A file that defines no language says so in its first line**, so it is not
   read as one under rules 1 to 3.

Lean's exhaustiveness checker enforces rule 1 on its side: adding a constructor
breaks every match that does not handle it. TypeScript has no equivalent unless
it is written, so the mirrors keep their case tables as records keyed by the
language's own union — `Record<Tag, true>`, `Record<ClauseKey, …>` — where a
missing key is a type error rather than a run-time refusal.

## The languages

| Language | Lean | TypeScript | Produced by |
| --- | --- | --- | --- |
| **Fragment** — the subset of TypeScript this pipeline accepts, as a tree | [Fragment.lean](lean/Verification/ExperimentState/Fragment.lean) | [fragment.mts](tools/fragment.mts), parsed by [fragment-parse.mts](tools/fragment-parse.mts) | the parser |
| **Claim** — what a producer says a type is, and what a source annotation is written in | [Claim.lean](lean/Verification/ExperimentState/Claim.lean) | [claim.mts](tools/claim.mts), printed by [claim-text.mts](tools/claim-text.mts) | SKJS, `tsc-claims.mts` |
| **SourceClaims** — claims attached to source spans, producer-independent | [SourceClaims.lean](lean/Verification/ExperimentState/SourceClaims.lean) | [source-claims.mts](tools/source-claims.mts) | either producer |
| **Calculus** — terms, tags, call codes: the operational language | [Calculus.lean](lean/Verification/ExperimentState/Calculus.lean) | [calculus.mts](tools/calculus.mts) | extraction |
| **ControlFlow** — the program graph over those terms | [ControlFlow.lean](lean/Verification/ExperimentState/ControlFlow.lean) | [control-flow.mts](tools/control-flow.mts) | extraction |
| **TypeGraph** — positive types as labelled rows | [PositiveNormalization.lean](lean/Verification/ExperimentState/PositiveNormalization.lean) | [type-graph.mts](tools/type-graph.mts) | extraction |
| **Request** — the whole verification request | [RequestJson.lean](lean/Verification/ExperimentState/RequestJson.lean) | — | extraction |
| **Evidence** — certificates the checker validates | [ProgramCertificates.lean](lean/Verification/ExperimentState/ProgramCertificates.lean), [PositiveCertificates.lean](lean/Verification/ExperimentState/PositiveCertificates.lean) | — | proof search |
| **Diagnostic** — why an attempt did not succeed | in [RequestJson.lean](lean/Verification/ExperimentState/RequestJson.lean) | [diagnostic.mts](tools/diagnostic.mts), rendered by [diagnostic-view.mts](tools/diagnostic-view.mts) | the verifier |
| **SKJS operations** — the closed judgments SKJS records | checked by [SkjsOperations.lean](lean/Verification/ExperimentState/SkjsOperations.lean) | [skjs-operations.mts](tools/skjs-operations.mts) | SKJS |

Defining no language, and saying so: [Decode.lean](lean/Verification/ExperimentState/Decode.lean)
(source spans and JSON accessors several decoders share) and [span.mts](tools/span.mts).

## Where the rule does not hold, and why

- **TypeGraph** has no single Lean counterpart. `Clause` lives in
  `PositiveNormalization.lean` because the normalization proofs are stated over
  it, and moving it to buy a matching filename would separate a definition from
  the theorems about it. The mirror is named for the language; the Lean side is
  named for the proof.
- **SKJS operations** has a Lean module with the same name that is a *checker*,
  not a mirror. It verifies these judgments rather than defining them, so by
  rule 3 it is a consumer that happens to read this language rather than a
  second definition of it.
- **Request** and **Evidence** have no TypeScript mirror. Nothing outside the
  verifier reads them, so there is no second reader to keep in step — and no
  independent one either.
- **span.mts** mirrors only half of `Decode.lean`. TypeScript has no shared JSON
  accessors, because each language file validates its own shapes.

## Known gaps

- **Nothing types SKJS's raw export document.** `skjs-operations.mts` declares
  one record from it and `source-claims.mts` declares the independent sidecar,
  but the raw document — functions, parameters, entries, expressions — is read
  structurally, so tools index into it untyped. A field SKJS renamed would
  surface as `undefined` at a use site rather than as a compile error.
- **The producer direction is unguarded.** The case tables above protect readers
  of a language. A producer that fails to emit a new case degrades to a refusal,
  which is a worse outcome reported honestly rather than a wrong one, but it is
  not a compile error and no table forces it.
- **`report-viewer/tsconfig.json` cannot run** on the `tsc` resolvable from that
  directory: it sets `erasableSyntaxOnly`, which needs 5.8, and 5.7.3 resolves.
  The files it covers are type-checked through `tools/tsconfig.json` regardless.

## Adding a language

Name it, give it a file on each side that it alone owns, and add a row above. If
it needs a case table in a mirror, key the table by the language's own union so
the next person cannot half-add a case. If the new file defines no language, say
so in its first line.
