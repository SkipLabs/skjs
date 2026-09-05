# Independent verification of SKJS results

This is an experiment in checking SKJS's answers without proving the whole SKJS
implementation correct. SKJS emits **type claims**. A smaller Lean verifier
checks them against an independently parsed source program.

The initial fragment, F0, is implemented. The calculus and verifier have
soundness proofs, and the test pipeline runs end to end. Broader language
support and integration into the ordinary SKJS command are future work.
See the [README](README.md) for setup, commands and the code map.

## Organization

Verification is organized as obligation generation and discharge:

| Part | Responsibility |
|---|---|
| **Source annotations** | Parameter, return and local annotations specify the required types. |
| **Type claims** | SKJS's inferred expression types and statement environments, supplying intermediate facts. |
| **Obligation** generation | Determine which relations must hold for those facts to justify typing. |
| **Obligation** discharge | Establish those relations, checking any supplied evidence. |
| **Calculus** | Define typing and execution and prove their connection. |
| **Input validation** | Locate the required claim entries and check duplicated source information. |

Source annotations and type claims are the two inputs, and they are not
interchangeable: an annotation is a requirement the program must meet, a claim
is a proposal about the program. A claim is never an assumption the verifier
may accept without justification. Proof hints may help establish a relation;
they cannot change the relation that must be established.

SKJS exports its type claims with `--emit-skjs-type-claims`.
In F0 a claim is a type together with the source identifier it applies to.
Later fragments may also carry **proof evidence**, such as subtyping
derivations, alongside the claims. **Certification** is the result of
successful verification.

## One example, end to end

Take this program, and follow it through every part of the table above.

```ts
function describe(x: string | number): string {
  if (typeof x === "string") {
    return x;
  }
  return "a number";
}
```

### 1. The trusted front end reads the source annotations

`parse-source.js` parses the file with the TypeScript compiler API, rejects
anything outside the fragment, and emits a syntax tree in which every node
carries its `[start, end)` character span. Two of those nodes are
**source annotations**: the parameter type `string | number` and the return
type `string`. They are requirements, and they come from the source, never
from SKJS:

```json
{ "name": "describe", "namePos": [9, 17],
  "params": [{ "name": "x", "pos": [18, 19],
               "type": { "top": false, "atoms": [{"a":"string"}, {"a":"number"}] } }],
  "retType": { "top": false, "atoms": [{"a":"string"}] } }
```

### 2. SKJS emits its type claims

`skjs check --emit-skjs-type-claims` produces a claim for every expression and
every statement entry, keyed by the same spans. These are proposals about the
program, not requirements on it:

```text
exprs   [61,62)   x  (inside typeof)      string | number
        [54,62)   typeof x                string
        [67,75)   "string"                "string"
        [54,75)   typeof x === "string"   boolean
        [90,91)   x  (returned)           string
        [106,116) "a number"              "a number"

envs    at 50     x: string | number      entering the `if`
        at 83     x: string               entering `return x`
        at 99     x: number               entering `return "a number"`
```

The environment claims also mention `this`, which the fragment cannot express;
the decoder drops such bindings, and a program that reads one is rejected at
the read.

### 3. Input validation binds the claims to the declaration

Before any typing, the verifier checks that this claim set is about this
function: the name and `namePos` must match, and the claimed signature must be
**equivalent** to the source annotations. The body is then checked against the
*source* annotation regardless, so this comparison is an audit of the claims
rather than something program soundness rests on.

### 4. Lowering discards the spans

`eraseProg` maps the source AST onto the calculus: `.bin .eq` becomes
`Core.Exp.eq`, spans disappear, and an absent `else` becomes an empty branch.
Everything proved from here on is about the lowered program, which is why the
final theorem mentions neither JSON nor source positions.

### 5. Obligation generation and discharge

The verifier walks the lowered body carrying its own environment, and at each
node it constructs an obligation and immediately discharges it. Following the
`return x` path:

```text
at 50    envCovers   x: string | number  ⊆  x: string | number   the claimed env
[61,62]  variable    string | number     ⊆  string | number      the claimed type
[54,62]  typeof      "string" | "number" ⊆  string               the claimed type
                     (the left side is tagsOf of the operand's type)
[67,75]  literal     "string"            ⊆  "string"             the claimed type
[54,75]  ===         boolean             ⊆  boolean              the claimed type
         condition   boolean             ⊆  boolean              an `if` needs a boolean

         --- narrowing: the true edge of the condition gives x: string ---

at 83    envCovers   x: string           ⊆  x: string            the claimed env
[90,91]  variable    string              ⊆  string               the claimed type
         return      string              ⊆  string               the declared return
```

Each line is one `Obligation.subtype`, discharged by `sub`. The narrowing step
is the calculus's, not SKJS's: the verifier derives `x: string` from
`typeof x === "string"` itself, and uses the claimed environment only to check
that SKJS did not narrow further than the rules justify.

Two of these lines are the reason a claim can fail. For the claimed type `T`
at `[90,91]`, discharge requires both

```text
string ⊆ T       T covers every value that can reach the expression
T ⊆ string       T fits the declared return type
```

`T = string` passes. `T = never` fails the first — the claim excludes a value
that really arrives. `T = unknown` fails the second. Neither failure needs the
verifier to know what SKJS was thinking; both are relations between types.

The false edge is checked the same way, with `x: number` derived from the same
condition, and `"a number" ⊆ string` at the return.

### 6. What acceptance establishes

Every obligation discharged, so `checkFile` returns `.ok ()`, and
`checkFile_sound` gives `ProgOk` for the lowered program. `Core.sound` then
says what that buys: calling `describe` with any value in `string | number`
cannot get stuck under the model, and if the call produces a value at all, that
value is a `string`.

What it does not establish: that SKJS computed those claims for the right
reasons, or that every claim is the type SKJS actually held internally. A claim
wider than necessary can satisfy every obligation and still be accepted.
Acceptance is a statement about the program, audited claims being the route to
it rather than the subject of it.

F0 is small enough that the verifier could infer these types without SKJS's
help; the calculus already includes a standalone checker. Using SKJS's claims
also lets the experiment check its answers. The value of supplied claims should
become clearer with loop invariants and generic instantiations, where finding a
suitable claim is harder.

## Current implementation

[Verify.lean](lean/Verification/Verify.lean) constructs each
`Obligation` and immediately calls `Obligation.discharge`. Generation and
discharge are fused in one traversal. There is no materialized obligation list,
external prover, or theorem about generation independent of discharge.

[Obligation.lean](lean/Verification/Obligation.lean) defines
containment and equivalence **obligations**, their semantic meaning, and a
**discharge** procedure built from the calculus's type comparisons. These
comparisons are sound; they do not decide every semantic inclusion.

Expression types are checked and then used in subsequent obligations. For
example, a call argument's claimed type must fit the callee's source parameter
type. The verifier derives branch environments itself, rather than relying on
the claimed ones.

Claimed environments have an additional check: every live binding the verifier
derives must appear in the claimed environment, with a type containing the
derived type. This catches unjustified narrowing, including a claimed
`never` for a reachable value.

## Program certification and claim auditing

There are two requirements:

- **Program certification:** acceptance establishes that the source satisfies
  the calculus.
- **Claim auditing:** the required claims satisfy their obligations, and
  duplicated signatures agree with the source.

The current verifier requires both, but its end-to-end soundness theorem
concludes program typing. It does not assert correctness of every claim at
every source position, nor agreement with SKJS's internal state.

For example, the verifier uses the source parameter type when checking a body.
It also requires the claimed parameter type to match. Removing that obligation
could leave program soundness intact while allowing inconsistent claims.
An input validation test guards that behavior.

Likewise, a wrong claim does not necessarily make a program unsafe. A broader
expression type may still satisfy every obligation. Acceptance and rejection
must therefore be described in terms of the required relations, not as a test
for every possible SKJS bug.

## Proof boundary

### Reviewing the definitions

The language definitions are organized around three questions:

- [Values.lean](lean/Verification/Calculus/Values.lean): what values exist?
- [Types.lean](lean/Verification/Calculus/Types.lean): what types exist, and
  which values belong to each type?
- [Programs.lean](lean/Verification/Calculus/Programs.lean): what expressions,
  statements and programs exist, and how do they execute?

Each language sits beside its semantics. `Values.lean` has no project imports;
`Types.lean` imports `Values.lean`, and `Programs.lean` imports `Types.lean`
because programs contain type annotations. None contains proof developments
or checking algorithms.

Then read [SourceAst.lean](lean/Verification/SourceAst.lean) for the supported
**TypeScript source** representation, with source locations. The mapping into
**programs in the core calculus** is in [Lowering.lean](lean/Verification/Lowering.lean).
Start at `eraseProg`, which translates a program by translating each function;
`eraseFn`, `eraseStm` and `eraseExp` handle functions, statements and expressions.
This translation determines which program the theorem describes.

The intended separation is:

```text
TypeScript text → SourceAst ──Lowering──→ calculus Programs → modeled execution
```

As TypeScript support grows, prefer translating source constructs into existing
core constructs where that preserves their behavior. A larger source language
does not necessarily require a larger calculus. This keeps the semantic
definitions and their proofs manageable. Some features will still need new
core constructs or semantics; the current fragment does not establish how far
translation alone will suffice.

Keeping the calculus small does not remove the need to review the translation.
The current theorem establishes safety of the translated core program; it does
not separately prove that the translation preserves TypeScript behavior. More
substantial translations would need corresponding justification, through review
and tests or a preservation proof where the source semantics is formalized.

The remaining calculus modules contain type operations, narrowing, typing
rules, soundness proofs and a standalone checker. `Calculus.lean` only imports
those modules, preserving the existing import path.

Each module has a test file under `Tests/` named after it, built by the
existing build command. A test file's header says which definitions it pins
and whether they are in the trusted base, because the two cases call for
different tests. For a trusted definition the checks are the only evidence
there is: nothing else in the project runs the evaluator, and soundness does
not constrain it (`execB … ≠ .stuck` holds for an `execB` that always times
out). For a derived definition soundness is already proved, so the checks pin
*precision* instead -- a `sub` that always returns `false` and a `narrow` that
changes nothing satisfy every proof in the development.

These definition files are the starting point for semantic review, not the
whole trust boundary. The parser and JSON decoders must faithfully represent
the source, and the execution model must agree with JavaScript. Those
assumptions remain as described below.

### What is proved

The key results are:

| Result | Meaning |
|---|---|
| `Obligation.discharge_sound` | A successful type comparison establishes the obligation's semantic meaning. |
| `checkExp_sound`, `checkStmts_sound`, `checkFile_sound` | The traversal, with obligations discharged as generated, establishes the calculus's typing judgements. |
| `Core.sound` | A well-typed program cannot get stuck under the model; returned values satisfy the declared return types. |

The file-level theorem is:

```text
checkFile funs claims = .ok () → ProgOk (eraseProg funs)
```

The theorem quantifies over arbitrary claim data. Its conclusion is about
the program obtained by erasing positions from the input AST. It does not
mention JSON, source files or SKJS.

The development has no `sorry` or project-specific axioms. Lean can report the
dependencies with `#print axioms Verification.checkFile_sound` after importing
`Verification.Verify`; the existing proof uses Lean's standard axioms
`propext`, `Classical.choice` and `Quot.sound`.

The remaining boundary is:

- The independent front end must faithfully represent the source.
- JSON decoding must preserve the intended input meaning, particularly the AST.
- Lean's kernel and compilation toolchain, and the executed binary, must be
  correct.
- The execution model must match JavaScript for the inputs being claimed.

The model uses a fuel-bounded evaluator with results for a returned value,
getting stuck, and running out of fuel. The proof rules out getting stuck;
it does not prove termination.

Numeric model agreement remains a limitation. Numbers are represented by double
bit patterns, with signed zero normalized. The model's truthiness treatment of
NaN differs from JavaScript, and its value equality also uses bit patterns.
The absence of arithmetic does not exclude NaN arriving through a `number`
parameter. The current Node sampler uses ordinary numbers and does not settle
these edge cases. The Lean theorem remains a theorem about the defined model.

## Claim format and source association

[SkjsTypeClaims.sk](../src/SkjsTypeClaims.sk) claims expression types from SKJS's
internal expression results, environments captured at statement entry, and
function signatures. Verification does not assume these claims are faithful to
what SKJS actually computed.

The JSON is an array of file entries. Each file has a `file` key and a
`functions` array. Each function contains:

| Field | Content |
|---|---|
| `name`, `namePos` | Function name and its source span. |
| `params`, `retType` | Claimed signature, checked against the source. |
| `exprs` | Expression span and claimed type. |
| `envs` | Statement span and claimed variable types. |

Types use `{top, atoms}`: `top: true` means `unknown`; otherwise the type is
the union of the atoms, with an empty list meaning `never`.
`{unsupported: true}` marks a type the fragment cannot represent.
Required unsupported expression or signature types reject verification.
Unsupported environment bindings are omitted during decoding into the usable
environment; a required binding must still be present.

Expression lookup uses the full span. Environment lookup uses the statement
start because the two parsers disagree on whether a trailing semicolon belongs
to the statement span. File keys and declaration spans associate claims with
the expected source nodes.

This is not source-content authentication. Extra expression and environment
entries need not be consumed, and two source texts can share positions.
Regardless of which claimed type lookup finds, the verifier must justify it
against the independently parsed AST.

The decoder implementations in
[JsonDecode.lean](lean/Verification/JsonDecode.lean) define the exact format.
There is no claim cache or production certification command in this
experiment; the harness generates claims for each run.

## Evidence from the experiment

`make verify-programs` runs the TypeScript program corpus, `make verify-claims`
the verifier's claim validation tests, and `make verify` both. They share setup
but report separately because they exercise different requirements.

The corpus exercises accepted programs, ordinary SKJS rejections, unsupported
syntax, and a known unsound acceptance. The
[beyond_precision](tests/programs/known-unsound/beyond_precision.ts) fixture
reproduces the numeric-literal problem associated with issue #781: two decimal
spellings denote the same double, but SKJS's narrowing treats them as different.
Verification rejects the claimed narrowing, and a sampled Node call violates
the declared return type.

The receiver tests alter a valid claim set. Obligation cases change claimed
types; input validation cases change signatures, required bindings or source
identifiers.
Each negative case requires the intended diagnostic. These are regression
tests of specific requirements, not additional soundness proofs.

Earlier manual experiments introduced errors in `evalCond`'s negation case,
`STypes::isSub`, and `evalTypeofEquality`. That experiment found that the
resulting claims were rejected. The three programs remain in
`tests/programs/reject/`, but the mutation harness is no longer present.
There is no standing exporter-faithfulness test. Changes to what SKJS records
internally, or to emission timing, can invalidate that evidence even if the
JSON format stays the same.

The runtime harness checks return values for sampled arguments, not full
equivalence between Node and the model. Test success should be interpreted
within those limits.

## Next experiment and later directions

The next language experiment is mutable locals, joins and loops, provisionally
called F1. This should test whether SKJS can supply useful invariants without
the verifier reproducing its inference machinery.

A claimed loop environment must hold on entry and be preserved by every back
edge, including `continue`. The loop condition must justify the body and exit
paths; writes must update or invalidate refinements soundly. Branch joins and
`break` paths need their own obligations. The exact policy is still design
work, not an implemented guarantee.

Before claiming that extension works, add the syntax and semantics, close its
soundness proofs, verify representative accepted programs, and reject incorrect
invariants for the intended reasons. Merely rejecting loops at the grammar gate
would not establish loop verification.

Other open work is to strengthen numeric model validation, restore a repeatable
exporter mutation experiment, and decide whether auditing every claimed
environment should have its own theorem. A materialized obligation list can be
introduced if discharging them separately, for testing or diagnostics, justifies it.

Later directions are higher-order functions and closures (F2), objects and
aliasing (F3), generics and classes (F4), then modules and ambient declarations
(F5). These labels describe a tentative sequence. Their proof formats,
invalidation policies, performance and practical coverage remain untested.
Ambient declarations would introduce explicit assumptions about external code.

Production integration would require an SKJS command that only reports certified
success after verification succeeds. `--emit-skjs-type-claims` currently only
emits claims. The stable experiment command is `make verify`, independent
of these fragment names.
