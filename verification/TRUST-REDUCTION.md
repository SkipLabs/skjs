# Reducing trust

Potential future work, not a plan of record. It lists the bridges between a
TypeScript program and the proved theorem that rest on review rather than
proof, the ways each could be narrowed or proved, and how they compose with
the [ECMA-262 connection](ECMA-CONNECTION.md).

## The bridges

[`checkJson_safe`](DESIGN.md#what-verified-means) proves the extracted
calculus program safe. Between the source a user writes and that program,
four things are trusted ([trust surface](DESIGN.md#trust-surface)):

| Bridge | Where | What is trusted |
| --- | --- | --- |
| **Parser rewrites** | `tools/fragment-parse.mts` (TypeScript) | Its lowerings (`switch`, `for`, templates, enums, optional chains, patterns, `super`, the iterator protocol, shadowing renames, …) preserve JavaScript's execution; TypeScript's binder names each reference's declaration. |
| **Extraction** | `Source/SourceExtraction.lean`, `Source/Fragment.lean` (Lean) | The calculus program it builds from the Fragment AST means what the Fragment means: control flow, lexical binding, evaluation order, and the program point each claim attaches to. |
| **Declared types** | `tools/declaration-graph.mts`, `type-term.mts`, `computed-types.mts`; `Source/DeclarationGraph.lean` | A declaration or annotation is read as the type TypeScript means. |
| **Host** | intrinsics, library overlay, environment premises | Native code meets its stated types ([ECMA-CONNECTION](ECMA-CONNECTION.md), T2). |

Extraction runs inside Lean, so what is checked is exactly what it produced;
but no theorem states that it preserves the source's meaning, because the
Fragment AST has no semantics in Lean. Its faithfulness is a reviewed
definition, as the parser's is.

## Options, cheapest first

1. **Structural theorems about extraction.** Provable in Lean over the AST it
   already has, with no JavaScript semantics: every edge targets a node; slots
   are fresh; every variable reference resolves to the declaration it names;
   every claim sits at its source span; every early exit passes the finalizers
   it leaves. These rule out the binding and control-flow errors extraction can
   make without ruling out every semantic one.
2. **Rewrites move from the parser into Lean.** The parser emits an AST close
   to the source (statement-level `switch`, `for`, templates, `super`,
   patterns, the iterator protocol) and extraction performs the rewrites.
   Trusted TypeScript shrinks to reading syntax and TypeScript's name and type
   resolution; the rewrites become subject to (1) and (3). Where a rewrite is
   chosen by a TypeScript type (`%Iterate:K%`, `%ElementAt%`), stating its
   correctness exposes the premise it needs ("the value is a host `Set`"),
   which is how a forged host value is caught.
3. **A Fragment semantics and a preservation theorem.** Give the Fragment AST
   an operational semantics in Lean, written as JavaScript's statement-level
   rules, and prove extraction a simulation: every run of the extracted program
   corresponds to a run of the Fragment with related states, throws included.
   Faithfulness then rests on the Fragment semantics, which reads like the
   specification and is reviewable against it. With (2), it covers the
   rewrites too; without (2), bugs before the Fragment escape it.
4. **A meaning for declared types.** Reading a declaration is a separate
   bridge: a meaning for TypeScript's type syntax (the forms the reader admits)
   and a theorem that the reader's graph rows denote it. Neither (2) nor (3)
   covers it.
5. **The host**, by [ECMA-CONNECTION](ECMA-CONNECTION.md)'s T2: each
   intrinsic and overlay entry proved of the specification's built-in.

## How they compose

The [ECMA-262 connection](ECMA-CONNECTION.md)'s T1 relates the calculus to a
mechanized specification M. With (3), T1 splits in two: M simulates the
Fragment semantics, and the Fragment semantics simulates the calculus through
extraction. The first half is stated at the level of JavaScript statements,
closer to how the specification is written; the second half is (3).

| Option | Retires | Needs |
| --- | --- | --- |
| (1) structural theorems | binding, control-flow and claim-placement errors in extraction | nothing new |
| (2) rewrites in Lean | trust in the parser's rewrites | (1) or (3) to prove them |
| (3) Fragment semantics | extraction's faithfulness, relative to the Fragment semantics | a Fragment semantics |
| (4) declared-type meaning | the declaration reader's faithfulness | a meaning of type syntax |
| (5) host lemmas | the ECMA rows of the trust surface | M |

## Evidence

Errors of the kinds these options address have occurred in each bridge: a
jump's slot map resolving a binding by name, a default reading the rest
parameter no longer refused, and source keys spelling the model's reserved
keys (extraction, caught by (1) or (3)); `super` in a static member calling
the base's prototype method, and a program-built object passing for a host
`Set` (parser rewrites, caught by (2) with (3)); generic contracts erased by
the declaration reader (declared types, (4)); an unbounded `%Await%` and
native array contracts (host, (5)). Each was found by review or tests; none
by the proofs, which hold of the program the bridges deliver.
