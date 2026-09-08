# Producer-independent source claims

The comment notation and serialized source-claim schema below are proposals;
there is no implemented comment frontend yet. A strict, bounded
[calculus-label sidecar](SOURCE-CLAIMS.md) is now implemented separately from the
arbitrary-graph proposal below. The in-memory consumption boundary
is now separated: `SourceClaims.Function` contains calculus type candidates, and
`SkjsSourceClaims.translate` adapts SKJS exports before source extraction.
`extractNormalizedFn` accepts those candidates directly. The source CLI accepts SKJS exports and, through separate modes, the bounded
producer-independent sidecar. The independent calculus request and
certificate checker already exist; this proposal changes how source claims reach
that boundary, not which semantic rules establish acceptance.

A [display-only annotated report generator](ANNOTATED-SOURCE.md) is now available.
It accepts SKJS exports or an independent display-claim document and can freshly
verify SKJS-backed functions. Its `@verify-report` comments are output, not the
claim-input notation proposed here. Stored report statuses never supply evidence.

## One claim model, multiple representations

A source-claim document associates candidate types with source expressions and
statement entries. A human, SKJS, or another analyzer can supply those candidates.
Comments and a sidecar file are two representations of the same information.
Neither representation contains trusted assertions or proof evidence.

The normalized interface should reuse the existing positive type graph from
[REQUEST-PROTOCOL](REQUEST-PROTOCOL.md), rather than store SKJS atoms or introduce
a second semantic type language. Source attachment is a separate layer: graph
labels identify types, and source binding IDs identify values. Source extraction
resolves those bindings to calculus slots and produces the ordinary requests and
supplemental obligations. The independent consumer reconstructs these requests
and checks their evidence as today.

Conceptually the document contains:

| Field | Meaning |
| --- | --- |
| Schema version | The source-claim interface version, independent of certificate versions. |
| Source identity | File identity and digest of the exact source bytes. |
| Type graph | The current calculus's finite positive graph; type references are lists of labels. |
| Function identities | References to function declarations in that source snapshot. |
| Binding identities | References to parameters and local declarations, resolved lexically. |
| Entry claims | Statement identity and a map from binding IDs to type references. |
| Expression claims | Expression identity and its type reference. |

The arbitrary-graph encoding remains to be implemented; the implemented
`stateful-source-19-v1` sidecar fixes the graph and retains current name/position
identities. It should use strict field and
reference validation, including duplicate rejection, as the request consumer
already does. Producer names and source-level display names are optional
provenance, never typing assumptions. An independently supplied graph does not
expand the source adapter's supported language: every used source type and
operation still needs a supported translation and its required checks.

### Implemented first step

The current in-memory interface is bounded by `SourceTypes.graph` (19 labels);
it is not yet the arbitrary-graph document described above. Names and positions
also retain the current source adapter's scope restrictions. It removes producer
type JSON from claim consumption without prematurely freezing a sidecar format.
Source annotations still use the current source AST type decoder.

A candidate carries either a decoded calculus type or an explicit decoding
failure. SKJS can export unrelated unsupported bindings, including implicit
`this`; their failures remain unavailable rather than becoming invented types.
Using such a candidate is an error. Directly supplied type labels are checked
against the source graph's bounds. The future strict comment frontend must reject
unconsumed directives; preserving the existing export policy does not change
that proposed requirement.

`SourceClaimsTests.lean` supplies claims without SKJS type JSON, checks their
certificates, compares the resulting request with the SKJS-adapted equivalent,
and rejects narrowing, missing claims, invalid labels and reused evidence for
changed judgments. The existing real-export suite exercises the same normalized
consumer through the SKJS adapter.

## Suggested comment notation

The first comment form supplies the environment at entry to the immediately
following statement:

```ts
function example(flag: boolean): boolean {
  const cell: { value: boolean } = { value: true };

  /* @verify entry { flag: boolean, cell: Ref<boolean> } */
  if (flag) {
    cell.value = false;
  }

  /* @verify entry { flag: boolean, cell: Ref<boolean> } */
  return cell.value;
}
```

These illustrate attachment only; they are not a complete certificate or all
claims currently required by the source adapter. `Ref<T>` denotes the calculus's
invariant cell contract. It is not a TypeScript alias and does not assert that
arbitrary structural objects are plain cells. The source allocation/access
boundary still has to establish that interpretation.

Expression claims should require an explicit parenthesized target:

```ts
const result: boolean = /* @verify expr boolean */ (cell.value);
```

The directive attaches to that parenthesized expression's operand. The parser
must recognize the comment with the TypeScript scanner and resolve it through
the AST, rather than search text for the next identifier or infer an enclosing
expression. Without this convention, `cell` and `cell.value` can start at the
same offset but have different claims. Ordinary comments and whitespace may
intervene; an intervening source token that is not the required target is an
attachment error. For entry directives the target must be a statement in the
same enclosing statement list. Ambiguous, orphaned or duplicate directives are
errors, not ignored metadata.

Names in an entry comment resolve in the lexical scope at the target's entry.
A local being initialized is not yet an initialized binding there. Resolution
produces a declaration-based identity, not a string-keyed global variable.
Declaration identities are scoped to the exact source snapshot; shadowed names
must not collapse. Resolving their identities is necessary but does not, by
itself, enable shadowing in the current source compiler.

Comments shift source offsets. Extraction and any external producer must use
the same final snapshot. A sidecar for different bytes is rejected, even when
names or nearby text happen to match. Do not transplant old offsets after adding
comments. A digest prevents stale attachment; it does not prove source lowering
correct or authenticate the producer.

## Types and obligations

The initial textual type notation should cover the implemented source slice:
`null`, `boolean`, `true`, `false`, `never`, primitive unions, supported invariant
cells, and supported unary arrows. Type notation is interpreted in the claim
language, not by TypeScript's alias lookup or SKJS's internal normalization.
Unknown types and unsupported combinations must be rejected explicitly.

The normalized type graph can already represent more, including recursive
positive types. Surface recursive aliases, intersections and generic bounds
should be added only with a specified elaboration and applicable source rules.
The comment frontend must not promise all TypeScript type expressions or invent
semantic-normalization equations. It is acceptable for the normalized interface
to be more expressive than the first comment parser or source adapter.

An entry claim is a checked environment, not an `assume`. Every relevant incoming
path must justify it through the current program rules or checked graph edges.
An expression claim must hold under its checked entry context. Source annotations
remain separate requirements. Stable reference types in an entry claim do not
license retaining a mutable field's singleton refinement across a write or call.

The first version should not add a `requires` or `assume` directive. Function
inputs come from the source annotations, and their entry claims must follow from
those inputs. A future contract syntax would need to state explicitly which
obligations it places on external callers; an entry comment cannot quietly
narrow the set of inputs for which a function is verified.

## Completeness of the supplied claims

The extractor determines the required claim sites from the program, as it does
now. Missing required environments or expression claims cause rejection. An
empty comment list does not mean the whole function has been verified. Every
supplied directive must also be consumed at its resolved site or rejected, so a
typo or a misplaced annotation cannot disappear silently.

A later tool can generate omitted claims, including from annotations or another
analyzer, but generation is a producer operation. Its results must be explicit
in the normalized input and checked in the same way as handwritten claims.
Generation must not turn missing evidence into an implicit assumption. The
producer remains free to fail even when a derivation exists.

Internal points created by lowering do not need artificial TypeScript statements
just to host comments. The source adapter must give them checked obligations,
using the existing source-guided recipes or an explicitly specified internal
point interface. Source comments do not replace checks on synthetic operations.

## Implementation order and trust boundary

1. The in-memory normalized source-claim structure and SKJS adapter are implemented.
   Keep the existing corpus and malformed-claim checks green. Separate decoding
   SKJS types from consuming source claims; do not have the comment frontend
   manufacture SKJS JSON.
2. Give source attachment and bindings explicit snapshot-relative identities.
   Test nested scopes, parenthesized expressions, non-ASCII offsets, duplicate
   sites and stale sidecars. The source compiler's feature gates remain explicit.
3. Add a strict comment parser and a sidecar encoder for the same structure.
   Test that equivalent comment and sidecar inputs reconstruct the same required
   calculus judgments, including negative cases and omitted claims.
4. Add optional claim generation or rewriting as a separate producer command.
   Re-extract after any rewrite; do not modify the user's source as a side effect
   of checking it.

Parsing and associating claims with source constructs is part of the reviewed
source boundary. The type-notation elaboration must likewise be specified and
checked or included in that boundary: proving a judgment about the wrong
interpretation would not verify the written claim. Moving claims into comments
neither enlarges the allowed assumptions nor proves these source-boundary steps.
The independent evidence consumer and semantic soundness theorems remain the
foundation for the resulting calculus judgments.

SKJS also exports partial function snapshots on normal first-error body failures.
The optional `collection` metadata records completion, checking mode, recovery
quality and expression visits. It is provenance only, ignored by proof checking;
missing required claims remain missing obligations. See
[partial reports and repair](ANNOTATED-SOURCE.md#rejected-programs-and-partial-collection).
