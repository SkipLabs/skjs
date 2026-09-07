# Independent verification of SKJS results

This is an experiment in checking SKJS's answers without proving the whole SKJS
implementation correct. SKJS emits **type claims**. A smaller Lean verifier
checks them against an independently parsed source program.

The initial fragment, F0, is implemented. The calculus and verifier have
soundness proofs, and the test pipeline runs end to end. Broader language
support and integration into the ordinary SKJS command are future work.
See the [README](README.md) for setup, commands and the code map, and
[SEMANTICS.md](SEMANTICS.md) for the semantics the calculus is heading toward
and how far it is established.

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

### 4. Lowering compiles the body into a control-flow graph

`lowerProg` turns each function body into a list of nodes indexed by position,
each naming its successors. A `const` becomes `set`, a `return` becomes `ret`,
an `if` becomes `branch`. Both arms of the `if` name the *same* continuation
label, so a branch that falls through and the branch's other edge arrive at
one node with two predecessors: a join. Successors are `Option Nat`, and
`none` -- control leaving the graph without returning -- is what no edge check
can justify.

Lowering also resolves lexical binding. Each `const` allocates a fresh slot,
and expressions are renamed to refer to slots rather than source names,
because connecting a branch to its continuation would otherwise let a binding
declared inside the branch escape:

```ts
const x = "outer";
if (b) { const x = "inner"; }
return x;              // must read the outer slot
```

Both have type `string`, so no type check would notice. Renaming is what makes
the `return` read `x@0`.

A declaration binds throughout its block, not from its own statement onward,
so the slots for a block are allocated before any of its statements is
lowered:

```ts
const x = "outer";
if (b) {
  return x;            // the inner x, which has no value yet
  const x = "inner";
}
```

That `return` resolves to the inner slot, which nothing sets on that path, so
no environment can supply it and the read is rejected -- and were the graph
run, `venvGet` would find nothing and report `stuck`. JavaScript throws
`ReferenceError` there and TypeScript rejects the program. Resolving from the
declaration onward would instead have silently read the outer binding.

Two scopes are therefore recorded per node, and they differ exactly in that
window. **Resolution** is block-scoped and says which slot an expression
means. **Visibility** is declaration-scoped -- what SKJS records -- and says
which slot a claim's name means. A binding that visibility has shadowed but
that is still live is carried as a *hidden* binding, taking its type from the
claim at the declaration that shadowed it; bindings are immutable, so that
type cannot have changed since. Without this the outer binding's type would be
lost inside the block, and the edge leaving it could not re-establish what its
target still needs.

The claim JSON does not change.

Everything proved from here on is about the lowered program, which is why the
final theorem mentions neither JSON nor source positions.

### 5. Obligation generation and discharge

Every node's entry environment is the claim at the statement it came from,
translated into slots. The checks are what justify using it: each node is
checked against its environment, and each edge must carry the environment its
source derived into the environment its target was given.

```text
entry              x: string | number  ⊆  x: string | number   node 0's claim

node 0  branch
[61,62]  variable  string | number     ⊆  string | number      the claimed type
[54,62]  typeof    "string" | "number" ⊆  string               the claimed type
                   (the left side is tagsOf of the operand's type)
[67,75]  literal   "string"            ⊆  "string"             the claimed type
[54,75]  ===       boolean             ⊆  boolean              the claimed type
         condition boolean             ⊆  boolean              a branch needs a boolean
         true edge x: string           ⊆  x: string            node 1's claim
         false edge x: number          ⊆  x: number            node 2's claim

node 1  ret
[90,91]  variable  string              ⊆  string               the claimed type
         return    string              ⊆  string               the declared return
```

Each line is one `Obligation.subtype`, discharged by `sub`. The narrowing on
the two edges is the calculus's, not SKJS's: the verifier derives `x: string`
from `typeof x === "string"` itself, and the edge check is what licenses
continuing under node 1's claim.

An edge obligation is `Covers G H`: every value environment agreeing with the
source `G` agrees with the target `H`. So an edge may establish more than its
target requires -- forgetting a fact is sound -- but a binding the target
requires and the source cannot supply is not. When two edges arrive at one
node, both must independently cover its claim, which is how a join is checked
without a least upper bound on types. The calculus has `meet` and `diff` and
deliberately no join.

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
help. Using SKJS's claims instead also lets the experiment check its answers,
and it is the interface a later fragment needs: once a loop head has a back
edge, there is no forward pass that derives its environment, and a supplied
one checked against every incoming edge is what replaces the fixed point. The
value of that should become clearer with loop invariants and generic
instantiations, where finding a suitable claim is harder.

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
type. The verifier derives branch environments itself, and the edge check is
what licenses continuing under the claimed one.

Environment claims are not audited alongside a separately derived
environment; they *are* the environments the nodes are checked against, and
the entry and edge checks are what make that sound. A claim narrower than the
values that reach a node fails on the edge into it -- including a `never`
claimed for a reachable value.

Statements that cannot run are not lowered. They are not part of the program
the theorem is about, so they carry none of its obligations -- in particular a
`const` after a `return` is not required to have anywhere to continue to. The
claims SKJS emits for them are simply not consumed; SKJS checks every
statement whether or not control reaches it, so nothing it accepts is rejected
here on this account.

The declarations in unreachable code still take effect on scope, because they
still shadow.

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
- [Programs.lean](lean/Verification/Calculus/Programs.lean): what expressions
  and programs exist, and how do they execute? A function body is a
  control-flow graph, so joins -- and later loop heads and back edges -- are
  ordinary edges rather than shapes the syntax has to anticipate.

Each language sits beside its semantics. `Values.lean` has no project imports;
`Types.lean` imports `Values.lean`, and `Programs.lean` imports `Types.lean`
because programs contain type annotations. None contains proof developments
or checking algorithms.

Then read [SourceAst.lean](lean/Verification/SourceAst.lean) for the supported
**TypeScript source** representation, with source locations. The mapping into
**programs in the core calculus** is in [Lowering.lean](lean/Verification/Lowering.lean).
Start at `lowerProg`, which compiles each function body into a graph. This
translation determines which program the theorem describes, and it is doing
more than erasure now: it allocates labels, so an off-by-one produces a
well-formed graph with the wrong control flow, and it resolves lexical binding
to slots, without which a `const` declared inside a branch would remain
readable after it.

The intended separation is:

```text
TypeScript text → SourceAst ──Lowering──→ calculus graphs → modeled execution
```

As TypeScript support grows, prefer translating source constructs into existing
core constructs where that preserves their behavior. A larger source language
does not necessarily require a larger calculus. This keeps the semantic
definitions and their proofs manageable. Some features will still need new
core constructs or semantics; the current fragment does not establish how far
translation alone will suffice.

Keeping the calculus small does not remove the need to review the translation,
and the move to graphs increased what there is to review. The current theorem
establishes safety of the translated core program; it does not separately
prove that the translation preserves source behavior. Lean has both the
source AST and the generated graph, so this boundary is accessible to proof;
what is missing is an independent semantics for the supported source AST.
Today, review and [Tests/Lowering.lean](lean/Verification/Tests/Lowering.lean)
support trust in the translation by checking successor labels and which slot
each node binds and reads. The optional work below describes how some of that
trust could be replaced with proofs.

The remaining calculus modules contain type operations, narrowing, typing
rules and soundness proofs. `Calculus.lean` only imports those modules,
preserving the existing import path.

Each module has a test file under `Tests/` named after it, built by the
existing build command. A test file's header says which definitions it pins
and whether they are in the trusted base, because the two cases call for
different tests. For a trusted definition the checks are the only evidence
there is: nothing else in the project runs the evaluator, and soundness does
not constrain it (`run … ≠ .stuck` holds for a `run` that always times out). For a derived definition soundness is already proved, so the checks pin
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
| `checkNode_sound`, `checkNodes_sound`, `checkFile_sound` | The node and edge checks, with obligations discharged as generated, establish the calculus's typing judgements. |
| `Core.sound` | A well-typed program cannot get stuck under the model; returned values satisfy the declared return types. |

The file-level theorem is:

```text
checkFile funs claims = .ok () → ProgOk (lowerProg funs)
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

## Extending the fragment

Moving the core from blocks to a control-flow graph changed no supported
construct, and still rewrote `Verify.lean`, half of `Typing.lean` and all of
`Tests/`, grew `Lowering.lean` fourfold and deleted the standalone checker,
while `Values`, `Types`, `TypeOperations`, `Narrowing`, `SourceAst` and the
claim modules were untouched. The cut was that clean because the restriction it
lifted — every branch must return — was not a premise of a rule but the *shape*
of the definitions: `BlockOk` had no rule for completing normally,
`BlockOk.ite` duplicated the continuation structurally, and `checkStmts`
recursed on statement lists. The shape also concealed a defect, `execB` leaking
a branch's bindings into its continuation, which the restriction had made
unobservable.

So before each extension, ask whether a restriction is a **side condition**, a
premise to delete, or a **shape**, in which case work already expressed in
terms of it has to be redone. Shape changes are worth scheduling deliberately,
ahead of the features that need them, and carrying out the way this one was:
same language, new representation, trusted closure measured on both sides.

### Choosing what to extend

Two signals are available, and they disagree.

*Coverage* asks how much of the corpus a fragment could reach. Measured as
fragment closure — the 488 corpus files that use nothing outside a candidate
fragment, detected by pattern, so approximate — it says objects and then
generics are where the mass is:

```text
  42   8%   F0 as implemented            75  15%   + closures
  44   9%   + mutable locals, loops     203  41%   + objects
  66  13%   + arithmetic, templates     261  53%   + classes
  69  14%   + switch, throw, try        410  84%   + type declarations, generics
```

*Auditability* asks whether extending the fragment would let the verifier
catch something SKJS actually gets wrong. That is what the experiment is for,
so where the two disagree, auditability wins. The soundness ledger
(`docs/ledger.yaml`, 67 rows) is the evidence: 18 rows violated, with fourteen
runnable witnesses under `docs/deep-dives/issues/`.

Three gates decide whether a row is reachable by this pipeline at all.

**What decides an assumption is the semantics, not the ledger category.** If
the calculus models the behaviour a row assumes, verification can establish
what SKJS merely takes for granted. If the calculus assumes it too, verification
cannot independently confirm it, and no claim can carry evidence for it. On
that test, rows about the ambient runtime — `A-PROTO`, `A-PROXY`, `A-DDA`,
`A-HASINST` — and about SKJS's own implementation, such as `A-HASH`, are out of
reach today and belong to testing and runtime grounding; others may come into
reach as the model grows.

**A defect in inference machinery is visible only through its results.**
`MR-1`, `OBL-MONOTONE`, `L-SUB-TSINST`, `C-FREEZE-CACHE` and `RB-1` concern
substitution state, memo caches and freeze windows. Claims record types at
source positions, not the state that produced them, so the *cause* is out of
reach — but a wrong type it produces is not, and rejecting the consequence
without understanding the cause is an advantage of this arrangement, not a
limitation. What cannot be relied on is coverage: such a row is caught only on
the occasions when it yields a type the obligations reject.

**The exporter, not the calculus, is the binding constraint.** `claimTypeJson`
returns `unsupported` for object types, `void`, type variables, unexpanded
instances, and any union of more than one DNF clause. A calculus that can
express more than the exporter can claim gains nothing — the verifier receives
`unsupported` and rejects. So each step below has to *inspect* what the
exporter already supplies and extend it only where the target needs it — which
is not always a new type encoding. For the first step it is not: SKJS already
emits every type the witness needs. For objects it is, and a claim
representation for structured types has to be designed before the calculus can
use one.

### The targets, and what each costs

Witnessed rows that survive those gates, cheapest first, with the shape change
each requires.

**`L-LIT` — already caught.** Two decimal spellings of one double are kept
distinct, so equality narrowing types a live branch `never` and a number
reaches a `string` return. `tests/programs/known-unsound/beyond_precision.ts`
is rejected today. This is the existence proof that the arrangement works.

**`L-LOOP-CARRIED` — loops need no new control flow; mutable locals need
storage.** A pre-loop narrowing of an annotated binding survives a back-edge
write. Reduced to primitive locals and boolean loop control, and arranged so
the stale value escapes through the declared return type:

```ts
function f(): string {
  let x: string | null = "hi";
  let second: boolean = false;
  if (x !== null) {
    while (true) {
      const s: string = x;   // second iteration: x is null
      if (second) { return s; }
      x = null;
      second = true;
    }
  }
  return "ok";
}
```

SKJS accepts this with no diagnostics; Node returns `null` from a function
declared `: string`. The claims SKJS emits are enough to reject it, and need no
new type encoding — every type in them is already expressible, and the defect
is visible in the environments directly: the `while` head claims `x: string`,
and the statement after `x = null` claims `x: null`. The back edge carries the
latter into the former, and `Covers` requires a node's claim to be justified by
*every* incoming edge, so `sub null string` fails.

The two halves of this step are not the same size. **Loops require no new
control-flow representation**: back edges, `break`, `continue` and `switch` are
an edge and an obligation on it, which is what the block representation could
not express and what `Edge` was built for. **Mutable locals require a storage
representation** — initially cells holding primitive values only. That is a
small semantic design, and it should be written before implementation:
allocation, reads, writes, the declared type a cell is constrained by, and what
holds before initialization. It does not require object layouts, access paths,
or general closure types. Committing to cells now, rather than to a binding
that becomes a cell when captured, is what keeps closures from forcing a redo.

One existing argument has to be revisited under writes. Today a shadowed
binding retains its type across a block, justified in `Lowering.lean` by the
fact that a shadowed slot is unnameable and so unwritable. That survives
mutable locals, but the extension should state explicitly which retained facts
remain valid under writes rather than inheriting the immutability argument.

Completion criteria, so that "catch this row" is a concrete target:

- SKJS accepts the reduced witness and supplies usable claims — confirmed;
- the independent front end accepts its syntax, which today it does not
  (`only \`const\` bindings are in the fragment`);
- verification rejects it at the back edge, for the invariant rather than for
  unsupported syntax or a missing claim;
- a corrected counterpart, narrowing inside the loop, verifies;
- modeled execution produces the bad return, matching Node.

**`L-STALE-READ`, `L-CAPT-EVOLVE` — closures.** A closure body reads enclosing
narrowings that are stale at invocation, and a captured write to an evolving
`let x = null` binding goes unchecked. A closure can be a code identifier plus
captured bindings, so the program stays a fixed collection of code bodies and
`lookupFun` survives; what grows is the correctness condition — what it means
for a closure value to inhabit a function type, and what must hold of its
captured environment.

**`L-MUT-ALIAS` — objects, aliasing, and the heap.** A field write through one
mutable view must preserve what every live alias of the same object was
promised. `Val` gains a store and references: threading an updated heap through
the evaluator is easy, and reference equality needs no special treatment, since
structural equality on a value carrying a location already expresses identity —
comparing referenced *contents* is what would be wrong. The exporter needs a
claim representation for object types. Access-path refinements — `x.kind === "a"`,
`"k" in x` — need *not* come with the first object fragment; a deliberately
less precise one can come first. The hard part is neither of these; see below.

**`L-INTER-BOT`, `F-CABSENT` — function and callability types.** Intersecting
two function types with incomparable signatures yields `never` although the
semantic intersection is inhabited, and `CAbsent` fails to exclude callables.
Both need structured types in `Ty` and in claims. What that costs is not
settled: recursive types, higher-order types and mutable contents each need
their own semantic decisions, and the atom-containment argument `atomMeet`
relies on does not survive any of them. Treat this as a direction, not a design.

Two things are worth naming as *not* on this list. Exceptions are not settled
by having a graph: a `throw` needs exception values, the state at the point of
raising, and abrupt completion, and `finally` can replace a pending return or
exception, which makes pending completion part of what the semantics carries.
And making calls explicit graph nodes is architectural rather than necessary —
an evaluator can thread a heap left to right through short-circuit operators —
but it gives effects, exceptional exits and intermediate claims definite places
to attach, at the cost of moving evaluation order and intermediate binding into
lowering, where they then have to be tested.

### The open design question

For `L-MUT-ALIAS` the delicate decision is not how to thread a heap through
theorem signatures. It is what invariant connects the heap to types, and that
splits into two obligations which must not be conflated:

1. **Well-formedness.** A write preserves the storage and aliasing guarantees
   the type system depends on — that each location keeps whatever stable type
   constrains it, and that every live view of it still holds.
2. **Retained refinements.** After the write, the flow-sensitive facts still
   carried about that location remain justified.

A conservative answer to (2) — discard every property refinement on any write
through an unknown reference — is sound and cheap, and it does **not** discharge
(1). Forgetting stale observations says nothing about whether the write itself
respected what another alias was promised.

The questions to settle, in that order:

- Is each storage location constrained by a stable declared type?
- What does a write through one view guarantee to every other live view?
- Which facts about an aliased variable survive a write, and when may a write
  refine what is known about the contents?
- What does a call tell the verifier about the locations it might change?

These decide whether the preservation proofs stay manageable, and they decide
what SKJS would have to supply. The effort belongs here, before any theorem
signature changes.

### The semantics

A recursive type has to mean something before a checker can be trusted about
it, and once the language can write, membership has to be relative to a world of
declared contracts rather than to heap contents. The construction, the four
properties it must satisfy, and what has been established are in
[SEMANTICS.md](SEMANTICS.md).

In short: a type is a family of approximations indexed by a budget; the budget
is spent only where the program spends one, at a dereference or a call; recursion
is the Banach fixed point of a contractive operator, which survives recursion
through argument positions where neither the least nor the greatest fixed point
exists; and values are judged against stratified worlds, with a separate
invariant tying an actual heap to the world. That combination is established for
a small stateful fragment — recursive reference types with an inhabited cyclic
heap, allocation, mutation through aliases, closures over mutable cells, and a
recursive function type — and not beyond it.

Within that fragment two questions are closed. For closed types built from
`null`, `bool`, invariant references and function types, semantic equality **is**
bisimulation of the corresponding finite guarded graph, in both directions — so
a finite certificate is complete evidence, and there are no further equations to
find. And once unions are added in operand position, semantic **inclusion** is
exactly clause-to-clause covering: each clause of the source matched by one
clause of the target, references invariantly and arrows contravariantly. That
is a subtyping result, and it holds for a reason specific to this language —
arrows do not split over unions, because a mutable cell is the branch a type
test would have provided. See
[COMPLETENESS-INVESTIGATION.md](COMPLETENESS-INVESTIGATION.md); the boundaries
are the interesting part.

### What remains between this and a usable calculus

Four pieces, in increasing order of design risk rather than of effort.

**1. Finish the operational interface.** Safety under decreasing budgets, the
remaining evaluation-context rules, and an adequacy theorem: a verified closed
program cannot get stuck. The application rule currently extracts a function's
guarantee at a strictly smaller index, which is not yet the general typing rule
for arbitrary expressions under environments; term substitution likewise needs
its binding discipline stated rather than relied on for closed arguments.
Necessary proof work, low architectural risk.

**2. Interpret an actual type language.** Two representations are on the table
and they are not interchangeable.

*Graphs* — a finite system of guarded equations — already carry the recursion,
exclude unguarded definitions by construction, and come with the completeness
result above. What they cannot express is anything open: no free parameters, no
schemes, no substitution.

*Binder syntax* is what a source translation naturally produces, and it needs
the missing bridge: admissibility of interpreted types, a substitution theorem,
recursive unfolding as the intended type equation, and an explicit guardedness
policy saying which definitions are admitted and why their interpretations
exist, rather than discharging that afresh at each use. This is where the
binder/world interaction is shown repaired *at the language level* — an equation
about a directly constructed family does not establish substitution through an
open recursive type.

The two meet at a translation, and the translation is where a real gap sits.
SKJS represents types as **named declarations with arguments, expanded on demand
under a depth cap**, which denotes a regular tree only while the parameters do
not grow. `type T<X> = { next: T<{ v: X }> }` is accepted by SKJS and is *not* a
finite graph. So graphs cover the closed regular types over the four-constructor
signature exactly, and a generic alias whose argument grows leaves even that
class — quite separately from the signature gap between those four constructors
and real object, union and literal types.

Two things about the rules are already settled. The cycle must be discharged by
induction on the budget, with an assumption citable only after a guard has been
crossed — and that has to be enforced by the shape of the rules rather than
checked afterwards, or a derivation can justify its own conclusion. And a cyclic
assumption reached through an argument position is needed in the orientation
opposite to the one that created it, so assumptions are unordered pairs and the
rule for `μ` establishes both directions.

One consequence is worth knowing before designing the relation: until the type
language has a top, a bottom or unions, subtyping so specified **coincides with
equality**. Contravariance is then unobservable and the both-directions
requirement costs nothing. The interesting design questions start with the
lattice, not with the recursion — and the first step into that lattice, unions
in operand position, is now taken: the rule for it is clause-to-clause covering
and it is complete.

**3. Resolve what can still change the design.**

*Intersection, difference and narrowing come first*, and are the next gate:
equality is settled without them, unions are settled with a complete rule, and
these change the theory rather than extending it. The vacuity they bring is
already visible — an everywhere-empty argument type makes `0 → A` and `0 → B`
equal, which is why the union rule waives the comparison at an empty operand and
why a cell declared at `never` is excluded by well-formedness rather than
handled. Give the Boolean layer its own equational theory rather than trying to
preserve tree equality after adding it.

Pointwise union and intersection preserve admissibility. Pointwise complement does not preserve downward closure, nor
monotonicity under world extension — so "interpret every DNF operation as the
corresponding set operation at each index" is not justified. The objective
leaves room here: a branch rule may use a sound approximation of the values
remaining after a failed test, and need not supply exact semantic
complementation of every higher-order type. Establish which operations the
calculus actually needs before buying a richer Boolean semantics.

*Mutable structural objects* need their own treatment. An invariant cell is a
foundation, not width subtyping, optional fields, readonly views, or a rule for
when mutation invalidates an established refinement.

*Generics and `extends` bounds* need less new semantics than expected. The
machinery is already present, and checked rather than assumed: a type variable is
a position in an environment of families, a bound is semantic inclusion between
families, and the quantifier is the intersection over admissible instantiations,
which is itself admissible whenever its instances are. Impredicative
quantification is free in this encoding, where a set-theoretic development would
need a universe bump or a domain construction. And a parameter under a reference
is already inhabited for every semantic type — the specific prerequisite the
earlier syntactic-world design failed.

What remains for generics as such is ordinary work: the fundamental theorem, that
one runtime function is safe under every admissible instantiation, which is what
universality means and which the reference-parameter result does not establish;
and variance for generic constructors, which nothing derives yet.

Two things are genuinely open, and neither is caused by quantification. A generic
alias whose argument grows leaves the regular-tree class altogether, so no finite
graph and no bisimulation certificate exists for it — and SKJS accepts such
declarations, so the calculus must refuse them, bound them as SKJS's expansion
cap does, or represent them some third way. And `∀` distributes over
intersections but **not** over unions, so a DNF representation of polymorphic
types cannot push the quantifier through the normal form and needs its own
justification. That is the Boolean layer again, which is why it comes first.

**4. Connect the calculus to checked invariants.** The deliverable is not SKJS
soundness but:

> if the calculus program and its supplied invariants pass verification, then
> execution satisfies the calculus's safety property.

That needs sound local instruction rules, sound checking of each incoming edge
against the supplied invariants, and a global execution theorem. Loops use the
supplied invariants; no inference and no computed fixed point is required.

SKJS remains a producer of candidate claims: its inference and its recursive
subtyping need no correctness proof of their own. Translating programs and
claims faithfully is a separate interface obligation.

### A bounded way to proceed

Enough of the above is speculative that a foundation built before anything
exercises it would be as likely to need revision as the block representation
was. Each step should end with a witnessed row caught, or with a design
question answered by something that runs.

1. **Mutable locals and loops, to catch `L-LOOP-CARRIED`.** The smallest
   fragment that reaches an unreached witnessed unsoundness, using machinery
   already in place. Cells from the start.

2. **Write the heap's semantic commitments down** — reference identity,
   storage locations, captured cells, and an initial invalidation policy with
   its precision limits — before changing any signature.

3. **Make calls explicit nodes**, if that is the intended long-term graph
   interface, while expressions are still small. Test evaluation order,
   short-circuit behaviour and intermediate binding in `Tests/Lowering.lean`,
   since they become lowering's responsibility.

4. **Introduce the heap with a program that uses it**, aimed at `L-MUT-ALIAS`.
   Allocation, a read, a write and two aliases to one location are enough to
   expose the choices above; a heap carried unchanged through primitive
   programs would be no evidence that the design works. Include a captured
   mutable cell as an early design test even if closure syntax comes later.

5. **Prove preservation for that stateful core before widening coverage**, and
   let what it costs decide whether property refinements or broader function
   values come next.

Steps 2 to 5 are provisional. What the storage invariant actually costs will
not be known until step 1 has been built, and that should be allowed to reorder
what follows it.

Each step extends the current calculus and pipeline; none requires a second
calculus or equivalence with a previous one. Remaining open work is to
strengthen numeric model validation, which arithmetic would force anyway, and
to restore a repeatable exporter mutation experiment.

Production integration would require an SKJS command that only reports certified
success after verification succeeds. `--emit-skjs-type-claims` currently only
emits claims. The stable experiment command is `make verify`, independent of any
fragment name.

### Optional: move the source-to-graph trust boundary

These are optional improvements to the current calculus and pipeline, not
requirements for adding another fragment. They concern the meaning of today's
source AST and its translation, not equivalence to a historical implementation.

1. **Prove structural properties of lowering.** Establish that emitted
   successor labels exist, allocated slots are fresh and cannot collide with
   source identifiers, and references resolve to the intended lexical binding.
   State the source well-formedness assumptions explicitly. Include declarations
   after a return: they still affect binding even though no graph node is emitted
   for them. Such theorems establish specific compiler properties; they do not
   alone prove preservation of execution.
2. **Define source-AST semantics and prove semantic preservation.** Give the
   supported `SourceAst` a direct execution meaning, including lexical scope,
   initialization errors, calls, and control flow. Prove that lowering preserves
   its observable execution outcomes, allowing different fuel consumption in
   the two representations. Combine that result with graph soundness to connect
   accepted claims to modeled source safety. This describes the input language
   of the existing pipeline; it does not introduce another verification pipeline
   or replace the graph calculus.

The second step would move trust from the lowering algorithm to the source
semantics and its agreement with JavaScript. That semantics would still need
review and validation. Faithfulness of the external parser to TypeScript text,
agreement with actual JavaScript execution, and Lean's trusted infrastructure
would remain outside this preservation theorem. Full TypeScript formalization
is not a prerequisite: the semantics can cover only the supported source AST.
