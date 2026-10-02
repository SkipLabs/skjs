# The pipeline's languages

Data crosses this pipeline as a sequence of distinct representations, each with
its own syntax. This file names them, says who owns each one, and records the
convention their files follow: a language whose file cannot be found is a
language whose cases get missed.

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
| **Fragment** — the subset of TypeScript this pipeline accepts, as a tree; its required `declarations` slot is emptied once Lean has interpreted its equations | [Fragment.lean](lean/Verification/Source/Fragment.lean) | [fragment.mts](tools/fragment.mts), parsed by [fragment-parse.mts](tools/fragment-parse.mts) | the parser |
| **Declaration graph** — the source type equations of every local and imported declaration a file reaches, with the declaration TypeScript binds each name to; function annotations are written in the same source type terms | [EquationLowering.lean](lean/Verification/Source/EquationLowering.lean) | [declaration-types.mts](tools/declaration-types.mts), read by [type-term.mts](tools/type-term.mts) and collected by [declaration-graph.mts](tools/declaration-graph.mts) | the parser, with TypeScript's checker |
| **Claim** — what a producer says a type is; source readers in Lean take annotations converted to it | [Claim.lean](lean/Verification/Types/Claim.lean) | [claim.mts](tools/claim.mts), printed by [claim-text.mts](tools/claim-text.mts) | `tsc-claims.mts`, [OCaml prototype](ocaml-producer/README.md) |
| **SourceClaims** — claims attached to source spans, producer-independent | [SourceClaims.lean](lean/Verification/Source/SourceClaims.lean) | [source-claims.mts](tools/source-claims.mts) | `tsc-claims.mts`, [OCaml prototype](ocaml-producer/README.md) |
| **Calculus** — terms, tags, call codes: the operational language | [Calculus.lean](lean/Verification/Semantics/Calculus.lean) | [calculus.mts](tools/calculus.mts) | extraction |
| **ControlFlow** — the program graph over those terms | [ControlFlow.lean](lean/Verification/Programs/ControlFlow.lean) | [control-flow.mts](tools/control-flow.mts) | extraction |
| **TypeGraph** — positive types as labelled rows | [PositiveNormalization.lean](lean/Verification/Types/PositiveNormalization.lean) | [type-graph.mts](tools/type-graph.mts) | extraction |
| **Request** — the whole verification request | [RequestJson.lean](lean/Verification/Source/RequestJson.lean) | — | extraction |
| **Evidence** — certificates the checker validates | [ProgramCertificates.lean](lean/Verification/Programs/ProgramCertificates.lean), [PositiveCertificates.lean](lean/Verification/Types/PositiveCertificates.lean) | — | proof search |
| **Diagnostic** — why an attempt did not succeed | in [RequestJson.lean](lean/Verification/Source/RequestJson.lean) | [diagnostic.mts](tools/diagnostic.mts), rendered by [diagnostic-view.mts](tools/diagnostic-view.mts) | the verifier |

Named fields cut across most of these at once, and they are named the same way
everywhere. An object is a finite map from field names to locations, fixed at
allocation: **Fragment** writes `{k:"alloc", fields}`, `{k:"read", field, e}`
and `{k:"write", field, receiver, rhs}`; **Claim** already had a record's
`fields`; **TypeGraph**'s `refs` and `callable` carry `[name, labels]` pairs;
**Calculus** has `objAt`, `makeAt`, `readAt` and `writeAt`; and a
**SourceClaims** `current` is a list of `[field, labels]` pairs, because what an
object holds is stated per field. No field name is privileged anywhere: `value`
is what a *mutable local's* own cell is called, an internal slot the lowering
invents, and what a source function's property bag is called, which is what
gives a function an identity to compare.

Callable **TypeGraph** signatures use one record with required `receiver`,
`arguments`, `result` and `effect` fields. Fixed signatures carry a list of
argument rows; variadic signatures carry the fixed prefix and rest contract.
Host-relative methods use the same record with an empty receiver object.
Effects are `unrestricted` or `preservesInputHeap`; no missing-effect default or
legacy tuple encoding is accepted. Source annotations produce unrestricted
contracts. A qualified producer claim additionally requires checked definition
evidence. The report viewer currently preserves qualified signatures as exact editable
JSON; the ordinary arrow text syntax cannot silently erase their effect.

Declaration-graph function terms also require `effect`: source TypeScript
annotations state `unrestricted`, while the reviewed native overlay can demand
a qualified callback. Graph lowering retains the field; conversion to the older
unqualified `Claim` arrow refuses a stronger effect rather than forgetting it.

Defining no language, and saying so: [Decode.lean](lean/Verification/Types/Decode.lean)
(source spans and JSON accessors several decoders share),
[span.mts](tools/span.mts) (the source span the fragment, the claims and the reports all carry)
and [thrown.mts](tools/thrown.mts) (the one reading of a caught value, which every tool reports the same way).

The [OCaml prototype](ocaml-producer/README.md) consumes the existing Fragment
and writes the existing SourceClaims document. Its internal typed view and
inference types are not additional wire protocols. OCaml pattern matches are
exhaustive over its implemented cases; unsupported source cases fail at decoding.
The shared Lean decoder checks every exported document. Cross-language protocol
drift currently causes a test failure/refusal, not an OCaml compilation error.

## Where the rule does not hold, and why

- **TypeGraph** has no single Lean counterpart. `Clause` lives in
  `PositiveNormalization.lean` because the normalization proofs are stated over
  it, and moving it to buy a matching filename would separate a definition from
  the theorems about it. The mirror is named for the language; the Lean side is
  named for the proof.
- **Request** and **Evidence** have no TypeScript mirror. Nothing outside the
  verifier reads them, so there is no second reader to keep in step — and no
  independent one either.
- **span.mts** mirrors only half of `Decode.lean`. TypeScript has no shared JSON
  accessors, because each language file validates its own shapes.

## Known gaps

- **The producer direction is unguarded.** The case tables above protect readers
  of a language. A producer that fails to emit a new case degrades to a refusal,
  which is a worse outcome reported honestly rather than a wrong one, but it is
  not a compile error and no table forces it.

## Adding a language

Name it, give it a file on each side that it alone owns, and add a row above. If
it needs a case table in a mirror, key the table by the language's own union so
the next person cannot half-add a case. If the new file defines no language, say
so in its first line.

Source allocations admit required, mutable, primitive-valued named fields.
The parser rejects `__proto__` initializers: JavaScript treats them as prototype
syntax rather than ordinary own fields. Fresh callable initialization also
rejects `call`, `bind`, `name`, `length`, `caller`, and `arguments`: these either
replace the intrinsics used by lowering or encounter special function properties.
These are source-language restrictions; the calculus itself has ordinary named
locations and does not model JavaScript prototypes or property descriptors.

TypeScript's producer exports these multi-field records; `records.ts` in the
corpus exercises them through the source pipeline and independent consumer.
