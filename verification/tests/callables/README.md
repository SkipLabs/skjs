# Callables

Source examples for callable contracts, checked through the parser, a claim
producer, the certificate producer, the independent consumer, and reports.
They have their own **Callables** group in the corpus and report viewer.

Add coverage for a distinct semantic obligation or an interaction that could
fail even when its components pass separately. Minor syntax variations alone
do not warrant another example. If a standalone Lean test takes too long to
develop or check, defer it until the case is expressible through the pipeline.

## The callable surface

The principal callable forms in the current roadmap, and where each stands. This is the
plan: a form leaves the table below only when a witness verifies through both a
producer and the independent consumer.

Supported. A function declaration is the checked unit and arrows are its callable
values; a call to a named top-level function is rejected by the source fragment.
Parameter lists of any length are checked, with the callee evaluated before the
actuals and the actuals left to right. A call may omit a trailing position
whose contract admits `undefined`, which is the value the machine binds there;
`x?: T` is carried as `T | undefined`. A parameter may instead carry a default,
`y: B = e`: its position admits `undefined` for the same reason, and `e`
replaces that value before the body runs, so the body reads `B`; a default may
read initialized earlier parameters. A rest parameter whose contract is a tuple
of required positions, `...rest: [B, C]`, is those positions in the signature
and one fresh array in the body, allocated where the parameter is bound. A
spread writes the elements of such a tuple in place of the last arguments, read
after every earlier argument has been evaluated. A rest parameter whose
contract is a mutable array, `...rest: T[]`, makes the closure variadic: it
takes any number of actuals past its fixed parameters, each at `T`, and the
call collects them into a fresh array. Spreads into it may stand anywhere among
those actuals, any number of them, each read where it is written: a spread
followed by an actual that runs code is copied there. An optional fixed
parameter before the rest may be omitted. A function type promises which actual
lists a caller may write, not which code the callee has, so a variadic closure
meets a fixed signature whose positions it admits, one value may carry fixed and
variadic signatures, and a callable object may be variadic. A current or later raw argument slot is
not a readable binding. Literal closures may capture later parameters through
acyclic closure conversion: their allocation waits until their captures are
initialized, and no executing initializer may read or expose a pending closure.
Effectful defaults retain source order. Quantified defaults, including inputs
of type `T | undefined`, have universal initialization certificates.
Callables pass as
arguments, return as results, escape as closures and appear as thunks; they form
unions with null and with each other, are selected by
`typeof x === "function"` guards, and are held in cells, including recursive
invocation through one. A fresh arrow takes one initialized `value` field through
explicitly typed `Object.assign`. `.call` applies to local arrows and their
immutable aliases, with the receiver evaluated and then discarded. `.bind` saves
an argument prefix on the same arrows. One closure may advertise several signatures — an intersection of arrows —
and is then checked once per signature, each a separate obligation on the same
body; its producer states what that body claims under each. TypeScript rejects
the implementations this accepts, so those witnesses are the OCaml producer's
alone. Rigid generic declarations
and bounds have source support. Quantified local closures have an independently
certified OCaml path; TS accepting their source does not imply its exporter can
represent their schemes. Keep those outcomes separate.

Not supported, with the refusal each one meets:

| Form                                                                                         | Where it stops                                                                                                                                                                                                                           |
| -------------------------------------------------------------------------------------------- | ---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `arguments`, argument-count introspection                                                    | the protocol excludes argument-count introspection                                                                                                                                                                                       |
| A spread of an array that may have holes into a rest whose element type lacks `undefined`    | named refusal: a hole spreads `undefined`, which the rest would hold; TypeScript accepts the call ([witness](../../pipeline/examples/spread-holes.ts))                                                                                                         |
| A spread into fixed parameters other than a last tuple spread                                | named refusal                                                                                                                                                                                                                            |
| Construct signatures, `new`, classes, accessors                                              | `function-constructible`; accessor execution is a separate semantic obligation                                                                                                                                                           |
| Index signatures and array brands on functions                                               | `function-index-signature`, `function-is-array`                                                                                                                                                                                          |
| Async functions, generators, function identity comparison, loops inside closures             | outside the fragment                                                                                                                                                                                                                     |
| Overloads through tsc | TypeScript rejects the implementation of an intersection-typed closure and states no per-signature interior claims; the OCaml producer states them |

Refusal reasons are defined in
[obligation diagnostics](../../OBLIGATION-DIAGNOSTICS.md); the encoding and its
restrictions belong to the
[protocol](../../REQUEST-PROTOCOL.md#expression-closures-and-calls).

The hole-spread witness writes past the end of a Boolean array, leaving a
hole. Spreading it would materialize `undefined` in a `boolean[]`. TypeScript
accepts this contract violation; the pipeline refuses the write.

### Closure status for milestones 1–4

1. **Optional positions:** implemented, with independent omission evidence,
   including a contract admitting undefined through semantic top.
2. **Overloads:** implemented with validated per-signature interior claims,
   including captured-field refinements. Each signature checks the same lowered
   body. Both CLI entry points reject malformed or misplaced rows.
3. **Defaults:** closed for this breadth milestone. Sequential initialization,
   generic defaults, and acyclic forward captures are implemented. Both formerly
   gated witnesses, `generic-rigid-default` and `default-deferred-capture`, now
   verify. The former also covers `T` containing `undefined` and a generic
   forward capture; the latter checks a capture chain across effectful defaults.
   Early invocation and a Boolean initializer falsely claimed at arbitrary `T`
   are negative controls. Both verifier entry points reject early invocation,
   and the report viewer receives a located refusal.

A default is an entry node of the code's graph: a tag dispatch on
`undefined` at the parameter's slot, the default's evaluation on one arm. The
slot's type is `T ∪ {undefined}` and the initialized binding's `T`; in a
generic closure the code is checked at its scheme row, so initialization must
establish `T` for every assignment of the binders, and observed calls cannot
justify it. It never obtains `T` by deleting `undefined` from the input: `T` can
itself contain `undefined`.

Forward capture support uses closure conversion in the trusted Lean extractor,
not a new mutable-world rule. A literal closure allocation can wait until its
captures are initialized because no pending closure is exposed and parameters
are immutable in this fragment. It is allocated once, preserving sharing, and
captures outer mutable cells by identity. All potentially effectful defaults
retain source order. `Fragment.parameterOrder` fixes the entry nodes' order,
and its dependency traversal is exhaustive.

This closes the planned breadth witnesses, not all JavaScript initialization
patterns. Cyclic captures and exposing a pending closure during initialization
are conservatively refused, even where a supplied actual could avoid the default.
Supporting those patterns later needs an explicit initialization frame with
initializedness separate from fixed world types; it must not expose raw actuals
or retype locations. The closure-conversion argument is part of the trusted
source adapter, as other JavaScript-to-calculus correspondence is; Lean proves
safety of the resulting term, not equivalence to a formal JavaScript semantics.

4. **Rest and spread: closed.** Fixed and variadic signatures share the
   behavioral call meaning. Array rests, ordered spread snapshots,
   variadic-to-fixed callback use, optional-prefix omission, callable fields
   and mixed signatures have checked witnesses. Quantified rests are graph
   code too, in declarations and local closures.
   Required tuple snapshots retain their dense contract; potentially sparse
   arrays still need an element contract admitting `undefined`.

The [common function equation](../../SEMANTICS.md#one-meaning-for-callable-contracts)
remains the foundation. Code collecting a rest allocates the store of the
further actuals before its run (`graphEntry`), and `restsT_of_graphRest` lifts
the code's check at each variadic signature to the variadic contract; over a
binder, at every assignment of it. Both declarations and closures are
consumed by `SourceClaimJson.checkJson_safe` as graph requests.

The OCaml producer's [`generic-rest.ts`](../../pipeline/examples/generic-rest.ts)
checks a returned `T[]`, independent Boolean and numeric uses of one closure,
a fixed prefix with empty rest and tuple spread, a universal default,
a possibly sparse spread, and a variadic callback inside a generic body.
The negative controls reject a captured Boolean array as arbitrary `T[]` and a
Boolean actual sent to a rest callback at arbitrary `T`. Both CLI entry points
reject altered rest contracts, substitutions, source binding flags and operand
claims; the report viewer renders the types and located failures. These are universal
certificates plus ground consequences, never observed-call monomorphization.

Tuple packs and argument-sequence inference remain later work, as planned.
The existing restrictions on generic body forms, nested quantification and
calls to top-level declarations remain explicit in
[SOURCE-CLAIMS.md](../../SOURCE-CLAIMS.md#quantified-callables-and-their-eliminations).
This milestone does not claim semantic completeness of direct subtyping.

### Order of extension

Breadth first, cheapest new representation first:

1. **`this` and methods**, following the receiver plan below: implemented, with
   `.bind`'s forwarding descriptor and `.apply`'s array-like preparation.
   Construct signatures follow separately.

### Receiver implementation plan

**Status: implemented, R1–R5, with the deviations and limits listed under
[implementation status](#implementation-status) below.** This section owns the
receiver design; [SEMANTICS](../../SEMANTICS.md#one-meaning-for-callable-contracts),
[PROGRAM-TYPING](../../PROGRAM-TYPING.md#judgments-and-constructor-views),
[REQUEST-PROTOCOL](../../REQUEST-PROTOCOL.md#receivers) and
[DESIGN](../../DESIGN.md#receivers) state the implemented rules.

#### Contract and runtime interface

Use one signature with separate components `receiver`, `parameters`, and
`result`, underneath any quantifier. A receiver is not parameter zero: it does
not change arity, optional positions, rest collection, or future `arguments`.
Use one native invocation `invoke(callee, receiver, actuals)` and a ready frame
carrying all three evaluated components. Retire the old call representation in
the same migration; any receiverless notation is an abbreviation supplying
`undefined`, not a second evaluator or protocol encoding.

The body frame is fixed as `[this, parameter_0, ..., parameter_n-1, captures...]`.
The runtime arity remains `n`; scope and substitution traverse a body under
`n + 1` binders. Argument padding/truncation applies only to the ordinary
parameters, after every actual has been evaluated. This layout must be shared
by `bindArgs`, closure scope, source slots and certificate environments.

Ordinary strict functions use the incoming receiver slot. Arrows ignore that
slot: a source occurrence of `this` resolves to an immutable lexical capture
from the nearest enclosing non-arrow receiver binding. Allocate that capture
with the other captures; do not snapshot the receiver's mutable fields.
Nested ordinary functions establish their own receiver binding. Thus an arrow
and an ordinary function can share the same core closure code representation
without sharing the source lookup rule for `this`.

Receiver-insensitive callable contracts have receiver family `top`; an explicit
receiver contract has its stated family. Omitting a receiver annotation is not
evidence that the body ignores `this`: initially require an explicit receiver
annotation on any ordinary function that uses it. Reject unsupported receiver
annotations rather than applying the existing discarded-result `void` conversion
in an input position. Arrow annotations cannot declare a dynamic receiver.

The first implementation admits ordinary receiver-dependent functions only when
the trusted parser establishes ECMAScript strict code, through a module or an
applicable directive prologue. TypeScript's `strict` type-checking option is not
that evidence. Record this source fact in the fragment and validate it on
consumption. An enclosing directive can cover methods without adding a directive
inside a function with default parameters. Sloppy receiver-dependent functions
stay a located source limitation until global-object substitution and primitive
boxing have operational rules; neither may be approximated by the strict rule.
This matches the distinction in
[OrdinaryCallBindThis](https://tc39.es/ecma262/#sec-ordinarycallbindthis).

#### Source calls, saved values and intrinsics

Source call targets must retain a typed distinction between a value and a
property reference. It is lost only when lowering constructs the explicit
receiver. Do not first lower `obj.method` to a bare callable value and try to
recover its receiver later. The parser preserves this distinction through
parentheses; a copied method is a value. This follows
[EvaluateCall](https://tc39.es/ecma262/multipage/ecmascript-language-expressions.html#sec-evaluatecall).

| Source                  | Lowering and required order                                                                                                     |
| ----------------------- | ------------------------------------------------------------------------------------------------------------------------------- |
| `f(a, b)`               | Save `f`, use `undefined` as receiver, evaluate `a` then `b`, invoke.                                                           |
| `obj.m(a, b)`           | Save `obj`, read and save its method, evaluate actuals, invoke the saved method with the saved object.                          |
| `obj[key](a)`           | Save object, evaluate key, read and save method, evaluate `a`, invoke. Initially retain the existing singleton-key restriction. |
| `(obj.m)(a)`            | Preserve the property reference and hence the receiver.                                                                         |
| `const f = obj.m; f(a)` | The saved value does not retain the property reference; pass `undefined`. A receiver-requiring signature must reject this call. |
| `f.call(r, a)`          | Establish the intrinsic lookup, save target, evaluate `r` then `a`, invoke with that receiver.                                  |
| `f.bind(r, a)`          | Establish the intrinsic, evaluate and save target, receiver and prefix now; allocate a bound callable.                          |

Give bound call code an explicit forwarding descriptor storing target, saved
receiver and saved argument prefix. Its call operation ignores the new receiver
and forwards prefix followed by newly evaluated actuals. Rebinding cannot
replace the first receiver. Ordinary object fields and this hidden bound state
are different; aliases cannot write the latter. Traversal/substitution and
admissibility must cover this constructor. This preserves a place for later
bound construction semantics; do not encode `new` as ordinary invocation or
pretend an ordinary wrapper has all bound-function behavior. See
[bound function invocation](https://tc39.es/ecma262/multipage/ordinary-and-exotic-objects-behaviours.html#sec-bound-function-exotic-objects-call-thisargument-argumentslist).

Keep the existing intrinsic provenance check. A structural callable type does
not establish that a property named `call`, `bind` or `apply` is the built-in.
Initially extend the known fresh-function/immutable-alias cases, with no writes
or shadowing of intrinsic properties or prototype mutation. Other cases fail
with a located limitation; they must not be silently lowered as intrinsics.
Actual accessor or proxy lookup remains outside this slice, not an effect-free
read justified by method syntax.

For `.apply`, first evaluate target, receiver and argument-list expression;
then read the list's length and indexed elements in order before invocation.
Null/undefined argument lists give zero actuals. Start with supported tuple or
array-like contracts and explicit length/element obligations; general accessors
and coercions stay gated. Share the eventual prepared actual list with ordinary
calls, but not the preparation algorithm with iterable spread. See
[Function.prototype.apply](https://tc39.es/ecma262/multipage/fundamental-objects.html#sec-function.prototype.apply).

#### Proof obligations and shared encoding

Write callable membership as `Calls(R, As, B)`: invocation is safe for every
receiver in `R` and ordinary argument list in `As`, at every admissible world
and heap. Establish the receiver premise at the final invocation world after
operand evaluation, using admissibility/world extension for saved values.
Do not preserve mutable receiver-field refinements across effectful actuals
unless existing checked heap transfer establishes them.

The introduction environment is `this : R, parameters : As, captures : Γ`.
An arrow's incoming `this : top` is unused and its lexical receiver retains
the captured contract. Elimination requires a separate receiver-typing premise
as well as the callee and ordered-argument premises. Subtyping is contravariant
in `R` and each ordinary input, covariant in the result:

`R₂ ≤ R₁, As₂ ≤ As₁, B₁ ≤ B₂` implies
`Calls(R₁, As₁, B₁) ≤ Calls(R₂, As₂, B₂)`.

A receiver-ignoring arrow can satisfy a more specific receiver requirement;
a receiver-dependent method cannot be widened to accept arbitrary receivers.
A method that writes a receiver field needs the existing write capability;
readonly access does not grant it, and the location's world type never changes.
Generic introduction quantifies over the receiver type along with the other
types, while retaining captured receiver identities and fixed location contracts.

Update the single shared callable signature in Lean, Fragment, SourceClaims,
TS export, OCaml semantic types, inference and
printing. Receiver constraints are input constraints, including variance reversal
when traversing callback types. No producer-specific receiver encoding or missing
field fallback is permitted. A forged `top` receiver must fail source/signature
comparison or body certification. Receiver failure is a structured obligation
with its source span, environment, actual type and required receiver type.

#### Execution order and closure conditions

| Step                     | Work and gate before proceeding                                                                                                                                                                                                                                                                                                                       |
| ------------------------ | ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| R1: core invocation      | Migrate call syntax, ready frames and binder layout in `Calculus`, `Bindings`, `CallArguments`, `Types`, `Safety`, and coherence traversals. Prove order, determinism, receiver/argument binding and invocation safety. Existing arrows acquire the explicit ignored slot.                                                                            |
| R2: certificates         | Thread receiver families and premises through positive graphs, creation/elimination rules, `ProgramCertificates` and scheme introduction/elimination. Extend exhaustive certification and rebuild `SourceClaimJson.checkJson_safe` with its exact CLI-success premise unchanged. No source method is accepted before this gate. |
| R3: source and producers | Add method/function expressions, strictness facts, lexical `this` resolution and reference-preserving call targets. Update all typed mirrors and display/editor syntax together. OCaml and TS witnesses must independently verify.                  |
| R4: binding              | Add the forwarding descriptor and prove receiver/prefix preservation and its residual signature. Integrate `.bind` and the existing intrinsic guards.                                                                                                                                                                                                 |
| R5: apply                | Add checked array-like preparation, retaining its effects and order, then reuse the proved invocation rule.                                                                                                                                                                                                                                           |

#### Implementation status

Strictness is checked at every source `this` read, including declaration entry
points. Arrow-body directive prologues affect nested code, but an arrow's
captured receiver retains its binding function's mode.

- **R1.** `Tm.invoke f r args` replaced the receiverless call; `call` and `app`
  abbreviate it with `undefined`. Ready frames carry the receiver, evaluated
  after the callee and before the actuals (`Step.callRecv`), and determinism,
  preparation and safety cover it. The body frame is the layout above,
  `[this, parameter_0, …, captures…]`, everywhere: `bindArgs`, closure scope,
  source slots and certificate environments; a variadic body has its rest
  array before the receiver. Arity, optional positions and rest collection
  are unaffected, since the receiver is not a parameter.
- **R2.** Signatures are `(receiver, parameters, result)` in graphs, wire,
  certificates (`ArrowCert.emptyRecv`, `recvUnion`; contravariant receivers),
  `ProgramCertificates` (receiver premise after the callee), generic
  certificates and schemes (`ClaimType.scheme` has `this`).
- **R3.** Function expressions and object-literal methods lower to lambdas with
  a receiver and a strictness fact; `this` resolves to the nearest ordinary
  function's receiver slot, an arrow's `this` being a capture; `o.m(a)` and
  `(o.m)(a)` lower to `invoke` on the saved object and method; every call's
  receiver is a located `method-receiver` obligation. Lean, Fragment,
  SourceClaims, the TypeScript producer, the OCaml
  producer's signatures and inference, claim text, the diagnostic view and the
  term codec all carry the receiver.
- **R4.** `CallCode.bound` with `Step.callBound`; `callsT_bound` and
  `restsT_bound` (residual fixed and variadic signatures at any receiver),
  `bound_ignores_receiver`, `rebind_keeps_receiver`; `HasTy.bindE`,
  `HasTy.bindRestE` and their evidence rules, with soundness and certificate
  completeness.
- **R5.** `.apply` saves target, receiver and list, then reads `length` and each
  index in order, then invokes; a list of unknown length is passed by its
  store's positions to a rest-only target; a missing, null or undefined list
  gives none.

Method calls take fixed and variadic signatures, spread actuals and element
targets as plain calls do; `.bind` takes fixed and variadic targets
(`bindRestE`, `restsT_bound`); `.apply` takes tuples, lists of unknown length
into a rest-only target, and nullish lists; a declaration's `this` parameter is
an assumed input; a named function expression is accepted where its body does
not refer to its name. The TypeScript producer states quantified closures and
reads each call's instantiation from the receiver and actuals it passes, so
every witness is verified by both producers. What stays refused is refused
for every function, not for receivers: sloppy code reading `this` (the plan's
later obligation), a function expression referring to its own name (a
recursive binding, as a cyclic closure initialization is), and inside a closure
body the array operations — element reads and spreads — that no closure call
has.

Required distinct witnesses: (1) property call versus extracted-method call;
(2) `.call` rebinding an ordinary method while an escaping inner arrow retains
the original receiver; (3) an actual replacing the receiver's method field,
showing the selected callee was already saved; (4) an actual mutating a receiver
field before the body reads it; (5) binding followed by mutation and rebinding,
showing saved identity, live fields and the original bound receiver;
(6) receiver write through a readonly view rejected; (7) forged receiver type,
dropped receiver premise and reused evidence after receiver substitution rejected;
(8) one generic callable instantiated with different receiver contracts without
retyping captured storage. For `.apply`, add ordered indexed reads and a control
that distinguishes them from iterator consumption. Each negative must reach its
intended check, not pass because the parser refused it.

Sloppy functions, `super`/home objects, construction/`new.target`, and
reflective bound-function properties stay explicit later obligations. The
receiver interface is shared with those future extensions; their semantics are
not implied by it.

## Examples

| Example in [unions.ts](unions.ts) | What it establishes                                                                                                                                                                                                            |
| --------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ |
| `guardedCallableUnion`            | A null guard permits calling either remaining signature and preserves both possible results.                                                                                                                                   |
| `andGuardedCallable`              | `&&` calls only the non-null function; its true result does not erase the skipped false result.                                                                                                                                |
| `orGuardedCallable`               | `\|\|` skips the call for null, preserving true alongside the callable's false result.                                                                                                                                         |
| `coalescedCallable`               | Null and undefined select a fallback function before invocation; either callable can supply the result.                                                                                                                        |
| `capturedGuardedCallable`         | A returned closure retains the immutable capture's non-null refinement and both callable alternatives after the branch ends.                                                                                                   |
| `aliasedCallableSelection`        | A selected local alias retains both callable alternatives through a nested closure; its callability does not transfer to the original nullable input.                                                                          |
| `sharedCallableDomain`            | A call must fit the shared argument domain of Boolean-accepting and true-only alternatives, while retaining both possible results.                                                                                             |
| `branchLocalCallableDomains`      | Branch-refined Boolean arguments satisfy different callable domains; neither branch facts nor singleton results can be transferred to the other branch.                                                                        |
| `callableArgumentWrite`           | An assignment used as a call argument checks both storage and parameter contracts; its false RHS admits an explicitly refined false-only callable view.                                                                        |
| `selectedCallableAfterMutation`   | A selected callable remains fixed while a shared-cell write changes its live capture. A same-typed callee substitution needs fresh evidence.               |
| `callbackProbeDoesNotNarrow`      | A Boolean-returning probe has no type-predicate contract: its true result cannot narrow the captured callback in the caller, whose own null guard remains required.                                                            |
| `ambiguousCaptureGuard`           | A successful disjunction may be justified by a separate Boolean flag; the returned closure must retain the nullable capture and guard it itself.                               |
| `compoundAbsenceCapture`          | A returning null-or-undefined guard must exclude both tags before closure creation. Both producers verify it.                                                                        |
| `twoAbsenceCapture`               | Eliminating undefined must retain null in a returned closure capture; its inner null guard is still needed. Both producers verify it.                       |
| `laterGuardedCallback`            | A guard after closure creation cannot refine its earlier capture; the closure needs its own guard. |
| `escapedLocalCallback`            | A returned closure captures a guarded nullable const whose declaration is wider than its initializer. Both producers verify it.                    |
| `distinctNullableCallbacks`       | Same-typed local callbacks require independent null guards.                                                     |
| `nullableFactoryResult`           | A factory result can mix a callable with null; both alternatives survive the factory contract and invocation, and the caller must guard the returned value before calling it.                                                  |
| `returnedCallableDomain`          | Factory branches with Boolean and true-only callable domains both implement a true-only result contract; neither the nested result claim nor a later call can widen that shared domain.                                        |
| `branchReturnedCapture`           | A factory returns different closures from a null-test branch; the escaping closure retains its own factory argument's refinement, which cannot transfer to the nullable caller capture.                                        |
| `nestedCallableArgumentWrite`     | A write inside a closure's call argument preserves the captured receiver and named RHS through temporary bindings; a same-typed capture cannot replace the parameter in the evidence.                                          |

The corpus checks each file's TypeScript claims through the same extraction
and independent consumer; the OCaml producer's own cases cover the same
features end to end ([`cases.mts`](../../pipeline/cases.mts)).

[factories.ts](factories.ts) contrasts factories allocating a private cell per
invocation with a control sharing a cell outside the factory.
[arguments.ts](arguments.ts) covers a stateful callback passed to an invoker and
`escapedCallbackArgument`, where that callback enters a wrapper factory, escapes
as a captured parameter, and returns through another invoker; an intervening
cell write distinguishes execution-time reads from creation-time snapshots. Its
`exchangeMultiArgument` transports a two-argument function through a mutable
cell and narrows its first domain on return.
[cells.ts](cells.ts) covers mutable callback storage: `replacedCallback`
distinguishes a saved function value from a later cell read after replacement,
and `recursiveCallback` installs a callback that reads and invokes itself
through the cell, then reaches a base case.
[thunks.ts](thunks.ts) covers zero-argument creation and invocation: a
returned thunk reads a cell after a write, and a saved thunk remains distinct
from its replacement.
[arity.ts](arity.ts) requires callee evaluation first, actuals left to right,
then the body; it also checks a returned closure capturing its second
parameter and a multi-argument union callee.
[guards.ts](guards.ts) selects callable signatures with strict
`typeof ... === "function"` and `!==` guards.

Overloaded closures are the OCaml producer's
[`overloads.ts`](../../pipeline/examples/overloads.ts), with
`invalid-overload.ts` claiming a signature its body does not implement. The
claims carry one interior set per signature, the same mechanism compiled scheme
eliminations use, and a block body is checked at each signature's own result
rather than at its one enclosing annotation.

[rest-arguments.ts](rest-arguments.ts) collects a tuple rest, reads it by
index, and spreads one in place of the last arguments, with and without fixed
arguments before it. A spread relies on the array's positions being what it
yields, which holds because this fragment cannot install an iterator of its
own. [variadic-arguments.ts](variadic-arguments.ts) collects an array rest in a
declaration and in closures, calls them with any number of actuals and with
several spreads among them, spreads a tuple into an array rest, passes a
variadic closure to a function that calls it, calls one through a fixed
signature, omits an optional parameter before the rest, gives one value fixed
and variadic signatures, and makes a variadic callable object with a field.

[optional-arguments.ts](optional-arguments.ts) omits an optional trailing
argument, writes it, and writes `undefined` for it; the three agree at run
time. [default-arguments.ts](default-arguments.ts) gives a parameter a
default, writes the argument anyway, and reads an earlier parameter in a
default. The lowering binds the parameter's own slot anonymously and binds its
name to the value that replaces an omitted argument, so no name is invented
and nothing shadows.

[call-objects.ts](call-objects.ts) holds an object with an ordinary method and
an arrow, extracts the method, and uses `.call` with a different object as
receiver: the method reads the supplied receiver, the arrow retains its
lexical capture, and changing either behavior flips the example's result. It
carries a `"use strict"` directive, the strict-mode evidence the receiver rule
needs. [methods.ts](methods.ts), [apply.ts](apply.ts) and
[generic-receivers.ts](generic-receivers.ts) carry the receiver plan's
required witnesses.

[function-field.ts](function-field.ts) initializes one mutable field on a fresh
arrow, writes through the original reference and reads/calls through an alias;
explicit `Object.assign` type arguments are required.
[receiver-call.ts](receiver-call.ts) brings `.call` on local arrows into the
pipeline, including an alias of a function with a field and a captured nullary
arrow. The receiver expression is evaluated before actuals even though its
value is ignored.

Run `make verify-test` for suites or `make verify-examples` for the corpus;
`make verify` runs both. The [test index](../README.md) describes suite ownership.
The [protocol](../../REQUEST-PROTOCOL.md#expression-closures-and-calls) owns
callable signature restrictions.
