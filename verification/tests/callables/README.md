# Callables

Source examples for callable contracts, checked through the existing parser,
SKJS claim exporter, certificate producer, independent consumer, and reports.
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
read initialized earlier parameters. A current or later raw argument slot is
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
an argument prefix on the same arrows through tsc's claims; SKJS rejects it
([finding](../skjs-incomplete/bound-arguments.ts)). One closure may advertise several signatures — an intersection of arrows —
and is then checked once per signature, each a separate obligation on the same
body; its producer states what that body claims under each. TypeScript rejects
the implementations this accepts, so those witnesses are the OCaml producer's
alone. Rigid generic declarations
and bounds have source support. Quantified local closures have an independently
certified OCaml path; TS accepting their source does not imply its exporter can
represent their schemes. Keep those outcomes separate.

Not supported, with the refusal each one meets:

| Form                                                                             | Where it stops                                                                                                                                                                                                                           |
| -------------------------------------------------------------------------------- | ---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| Rest parameters, spread actuals, `arguments`                                     | `function-rest-parameter`; the protocol excludes spread and argument-count introspection                                                                                                                                                 |
| `this` parameters, receiver-dependent methods, `.apply`                          | `function-this-parameter`; the calculus has no receiver, so `.call` discards one ([boundary example](call-objects.ts), [receiver plan](#receiver-implementation-plan))                                                                   |
| Construct signatures, `new`, classes, accessors                                  | `function-constructible`; accessor execution is a separate semantic obligation                                                                                                                                                           |
| Index signatures and array brands on functions                                   | `function-index-signature`, `function-is-array`                                                                                                                                                                                          |
| Function expressions as values                                                   | only arrows lower to `lambda`                                                                                                                                                                                                            |
| Async functions, generators, function identity comparison, loops inside closures | outside the fragment                                                                                                                                                                                                                     |
| Generic signatures through SKJS                                                  | `function-generic`: SKJS types quantified closures but exports them as unavailable, so the OCaml witnesses carry these rows                                                                                                              |
| Optional and defaulted parameters through SKJS                                   | `function-optional-parameter`: SKJS types them and exports every claim mentioning the signature as unavailable                                                                                                                           |
| Overloads through SKJS and tsc                                                   | both reject the implementation of an intersection-typed closure, and neither states per-signature interior claims; SKJS also collapses incomparable arrow intersections to `never` ([finding](../skjs-incomplete/arrow-intersection.ts)) |

Refusal reasons are defined in
[obligation diagnostics](../../OBLIGATION-DIAGNOSTICS.md); the encoding and its
restrictions belong to the
[protocol](../../REQUEST-PROTOCOL.md#expression-closures-and-calls).

### Closure status for milestones 1–3

1. **Optional positions:** implemented, with independent omission evidence,
   including a contract admitting undefined through semantic top.
2. **Overloads:** implemented with validated per-signature interior claims,
   including captured-field refinements. Each signature checks the same lowered
   body. Both CLI entry points reject malformed or misplaced rows.
3. **Defaults:** closed for this breadth milestone. Sequential initialization,
   rigid defaults, and acyclic forward captures are implemented. Both formerly
   gated witnesses, `generic-rigid-default` and `default-deferred-capture`, now
   verify. The former also covers `T` containing `undefined` and a generic
   forward capture; the latter checks a capture chain across effectful defaults.
   Early invocation and a Boolean initializer falsely claimed at arbitrary `T`
   are negative controls. Both verifier entry points reject early invocation,
   and the viewer receives a located refusal.

The universal certificate distinguishes an unreadable raw argument slot of
meaning `T ∪ {undefined}` from an initialized value binding of type `T`.
Initialization must establish `T` for every admissible assignment; observed
calls cannot justify it. The source claim uses an ordinary union, and scheme
compilation substitutes the initialized annotation separately from the input
contract. In particular it must not obtain `T` by deleting `undefined` from the
input: `T` can itself contain `undefined`.

Forward capture support uses closure conversion in the trusted Lean extractor,
not a new mutable-world rule. A literal closure allocation can wait until its
captures are initialized because no pending closure is exposed and parameters
are immutable in this fragment. It is allocated once, preserving sharing, and
captures outer mutable cells by identity. All potentially effectful defaults
retain source order. `Fragment.parameterOrder` is shared by ordinary lowering
and universal certificates, and its dependency traversal is exhaustive.

This closes the planned breadth witnesses, not all JavaScript initialization
patterns. Cyclic captures and exposing a pending closure during initialization
are conservatively refused, even where a supplied actual could avoid the default.
Supporting those patterns later needs an explicit initialization frame with
initializedness separate from fixed world types; it must not expose raw actuals
or retype locations. The closure-conversion argument is part of the trusted
source adapter, as other JavaScript-to-calculus correspondence is; Lean proves
safety of the resulting term, not equivalence to a formal JavaScript semantics.
Generic field-write defaults still await the generic effect certificate, an
independent restriction of generic bodies rather than a missing default rule.

### Order of extension

Breadth first, cheapest new representation first:

1. **Rest parameters and spread actuals.** Unlike the three rows above, this
   one is not type-level. A rest parameter collects its surplus arguments into
   a fresh array, and invocation does not allocate: `bindParameters` binds the
   prepared actuals and nothing else, so `Invoke`, the step relation and every
   proof about them would acquire a heap. Packing the surplus at the source
   instead is only sound when the callee really has a rest parameter, so the
   signature would have to record which position is the rest one — an inert
   marker inside a type whose meaning would not change, which is the kind of
   thing the clause language deliberately does not carry. Decide between the
   two before writing either; the rest of the fragment does not depend on it.
2. **`this` and methods**, following the receiver plan below. `.apply` then adds
   array-like argument preparation; it is not spread's iterator operation.
   Construct signatures follow separately. Decide the receiver interface now
   and use it when extending signatures in the steps above, even before source
   methods are admitted.

### Receiver implementation plan

**Status: design, not implemented.** This section owns the receiver design;
the semantic and protocol documents must acquire the implemented rules alongside
the corresponding code. The current calculus has no receiver. Existing arrows
and their ignored `.call` receivers do not establish method support.

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
SKJS conversion, TS export, OCaml semantic types, inference, claim editing and
printing. Receiver constraints are input constraints, including variance reversal
when traversing callback types. No producer-specific receiver encoding or missing
field fallback is permitted. A forged `top` receiver must fail source/signature
comparison or body certification. Receiver failure is a structured obligation
with its source span, environment, actual type and required receiver type.

#### Execution order and closure conditions

| Step                     | Work and gate before proceeding                                                                                                                                                                                                                                                                                                                       |
| ------------------------ | ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| R1: core invocation      | Migrate call syntax, ready frames and binder layout in `Calculus`, `Bindings`, `CallArguments`, `Types`, `Safety`, and coherence traversals. Prove order, determinism, receiver/argument binding and invocation safety. Existing arrows acquire the explicit ignored slot.                                                                            |
| R2: certificates         | Thread receiver families and premises through positive graphs, creation/elimination rules, `ProgramCertificates`, `GenericCertificate` and scheme introduction/elimination. Extend exhaustive certification and rebuild `SourceClaimJson.checkJson_safe` with its exact CLI-success premise unchanged. No source method is accepted before this gate. |
| R3: source and producers | Add method/function expressions, strictness facts, lexical `this` resolution and reference-preserving call targets. Update all typed mirrors and display/editor syntax together. OCaml and TS witnesses must independently verify; SKJS export refusals remain separately reported, with no checker change hidden in this extension.                  |
| R4: binding              | Add the forwarding descriptor and prove receiver/prefix preservation and its residual signature. Integrate `.bind` and the existing intrinsic guards.                                                                                                                                                                                                 |
| R5: apply                | Add checked array-like preparation, retaining its effects and order, then reuse the proved invocation rule.                                                                                                                                                                                                                                           |

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

Promote `call-objects.ts` from boundary to verified coverage only after adding
strict-mode evidence to that fixture and independently certifying both its
ordinary method and lexical arrow behavior. Extend the direct completeness
judgments with receiver premises wherever the direct checker accepts the new
forms; do not describe the old receiverless theorem as covering them. Keep
sloppy functions, `super`/home objects, construction/`new.target`, and reflective
bound-function properties as explicit later obligations. The receiver interface
is shared with those future extensions; their semantics are not implied by it.

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
| `selectedCallableAfterMutation`   | A selected callable remains fixed while a shared-cell write changes its live capture. A JavaScript witness distinguishes live from snapshot behavior, and a same-typed callee substitution needs fresh evidence.               |
| `callbackProbeDoesNotNarrow`      | A Boolean-returning probe has no type-predicate contract: its true result cannot narrow the captured callback in the caller, whose own null guard remains required.                                                            |
| `ambiguousCaptureGuard`           | A successful disjunction may be justified by a separate Boolean flag; the returned closure must retain the nullable capture and guard it itself. The tsc suite checks both alternatives survive.                               |
| `compoundAbsenceCapture`          | A returning null-or-undefined guard must exclude both tags before closure creation. Both producers verify it, and the tsc suite checks both exclusions.                                                                        |
| `twoAbsenceCapture`               | Eliminating undefined must retain null in a returned closure capture; its inner null guard is still needed. Both producers verify it; the tsc suite checks that undefined is removed while null remains.                       |
| `laterGuardedCallback`            | A guard after closure creation cannot refine its earlier capture; the closure needs its own guard. The tsc suite checks the pre-guard nullable claim, and a reversed inner guard fails independently of the later outer guard. |
| `escapedLocalCallback`            | A returned closure captures a guarded nullable const whose declaration is wider than its initializer. Both producers verify it; the tsc suite checks that its callee claim retains the creation-time guard.                    |
| `distinctNullableCallbacks`       | Same-typed local callbacks require independent null guards; the tsc suite checks that guarding the first leaves the second nullable, then each own guard permits its call.                                                     |
| `nullableFactoryResult`           | A factory result can mix a callable with null; both alternatives survive the factory contract and invocation, and the caller must guard the returned value before calling it.                                                  |
| `returnedCallableDomain`          | Factory branches with Boolean and true-only callable domains both implement a true-only result contract; neither the nested result claim nor a later call can widen that shared domain.                                        |
| `branchReturnedCapture`           | A factory returns different closures from a null-test branch; the escaping closure retains its own factory argument's refinement, which cannot transfer to the nullable caller capture.                                        |
| `nestedCallableArgumentWrite`     | A write inside a closure's call argument preserves the captured receiver and named RHS through temporary bindings; a same-typed capture cannot replace the parameter in the evidence.                                          |

[callables.mts](../callables.mts) checks original SKJS claims, forged claims,
reused evidence and report round trips. [tsc-claims.mts](../tsc-claims.mts) checks
the TypeScript producer, including the capture refinements identified above.
Both producers use the same extraction and independent consumer.

For `callableArgumentWrite`, SKJS exports Boolean for the assignment. A separate
false-result refinement verifies with fresh evidence; it is an explicit candidate,
not an original producer claim. Under `nullableFactoryResult`'s nullable context,
the tsc producer uses the lambda's own expression type, then checks that arrow
against the full return contract.

[factories.ts](factories.ts) contrasts factories allocating a private cell per
invocation with a control sharing a cell outside the factory.
[callable-factories.mts](../callable-factories.mts) rejects a narrowed returned
closure result with both fresh and reused evidence. Its JavaScript witness checks
that `first(true)`, `second(false)`, `first(false)` return false/false/true with
private cells and false/true/false with the shared cell. A passive observer records
the intermediate results; the unmodified function's result is checked too.

[arguments.ts](arguments.ts) covers a stateful callback passed to an invoker and
`escapedCallbackArgument`, where that callback enters a wrapper factory, escapes
as a captured parameter, and returns through another invoker. An intervening cell
write distinguishes execution-time reads from creation-time snapshots.
[callable-arguments.mts](../callable-arguments.mts) rejects incompatible callback
domains and results, and checks the escaping wrapper's JavaScript result for both
seeds. Both producers' certificates for factories and arguments are independently
checked.

JavaScript witnesses establish observations separate from the Boolean typing
certificates. They do not prove that extracted Lean programs execute equivalently;
those execution checks remain deferred unless a concrete discrepancy warrants
investigation. The [protocol](../../REQUEST-PROTOCOL.md#expression-closures-and-calls)
owns callable signature restrictions.

Core semantic regressions remain in `lean/Verification/ExperimentState/`.
`SourceCallableUnionTests.lean` isolates union decoding, operand-slot lowering
and overloaded union calls with explicit claims. Null and Boolean arguments
select different signatures in each alternative; narrowing the joined result or
omitting an alternative's compatible signature fails. These are not verified SKJS
exports: SKJS collapses incomparable arrow intersections to `never`, as recorded
in the [intersection finding](../skjs-incomplete/arrow-intersection.ts).
Guard polarity and guarded results are covered by the source suites; recursive
callable bags and recursive invocation remain distinct model obligations.

Run `make verify-test` for suites or `make verify-examples` for the corpus;
`make verify` runs both. The [test index](../README.md) describes suite ownership.

[cells.ts](cells.ts) and [callable-cells.mts](../callable-cells.mts) cover mutable
callback storage. `replacedCallback` distinguishes a saved function value from a
later cell read after replacement. `recursiveCallback` installs a callback that
reads and invokes itself through the cell, then reaches a base case. Both producers
verify the original claims with independent consumption. Forged read/write domains
and replacement result contracts fail; JavaScript witnesses check both seeds.
These examples require no new calculus constructor or typing rule.

[thunks.ts](thunks.ts) and [callable-thunks.mts](../callable-thunks.mts) cover
zero-argument creation and invocation: a returned thunk reads a cell after a
write, and a saved thunk remains distinct from its replacement. Both producers'
claims are independently checked. Forged domains/results fail, and the callable
argument suite checks that omission does not satisfy a required callback parameter.
JavaScript witnesses check delayed reads and replacement for both seeds.

[arity.ts](arity.ts) checks native argument lists through both producers and the
independent consumer. Its order-sensitive example requires callee evaluation
first, actuals left to right, then the body. The existing JavaScript controls
distinguish reversed argument order and delayed callee evaluation; reused
evidence rejects swapped actuals. The same file checks a returned closure that
captures its second parameter and a multi-argument union callee.

[arguments.ts](arguments.ts)'s `exchangeMultiArgument` transports a two-argument
function through a mutable cell and narrows its first domain on return. Both
producers verify it; the argument suite rejects a widened second domain and a
dropped second parameter. Required function **types** can now carry multiple
parameters through the source pipeline, with native call and lambda lowering.

Overloaded closures are the OCaml producer's
[`overloads.ts`](../../ocaml-producer/examples/overloads.ts), with
`invalid-overload.ts` claiming a signature its body does not implement. The
claims carry one interior set per signature, the same mechanism compiled scheme
eliminations use, and a block body is checked at each signature's own result
rather than at its one enclosing annotation.

[optional-arguments.ts](optional-arguments.ts) omits an optional trailing
argument, writes it, and writes `undefined` for it. The three agree at run time,
and the JavaScript witness in [optional-arguments.mts](../optional-arguments.mts)
establishes what omission means before any claim is read. Forging the optional
position's contract to drop `undefined` makes the same call fail, in the
consumer and in production: the licence to omit is the contract, and no actual
is invented to repair it. The tsc producer verifies all three functions; SKJS
types them and exports every claim mentioning the closure as unavailable
(`function-optional-parameter`), which the corpus records as its outcome.

[default-arguments.ts](default-arguments.ts) gives a parameter a default,
writes the argument anyway, and reads an earlier parameter in a default. The
lowering binds the parameter's own slot anonymously and binds its name to the
value that replaces an omitted argument, so no name is invented and nothing
shadows. The suite forges the default out of its parameter's contract and
removes `undefined` from the position it fills; both must fail.

[guards.ts](guards.ts) selects existing callable signatures with strict
`typeof ... === "function"` and `!==` guards. It covers a mixed runtime-shape
union, a returned thunk retaining a negative guard's refinement, and a call used
as the tested value. Both producers verify the examples; the guard suite rejects
opposite polarity, refinement of another variable, and an invented narrower
callable result. General string/typeof expressions remain outside the fragment.

[call-objects.ts](call-objects.ts) demonstrates an object containing an ordinary
method and an arrow, extracting the method, and using `.call` with a different
object as receiver. The method reads the supplied receiver; the arrow retains
its lexical capture. Both outcomes matter: changing either behavior flips the
example's result. SKJS and strict TypeScript accept it, and JavaScript controls
check both seeds.

This is a **boundary example**, shown in the Callables group but not counted as
source-verifiable. Multi-field objects are supported; the remaining boundary is
ordinary receiver-dependent methods and receiver-dependent `Function.prototype.call`
behavior. The receiver plan above owns its promotion criteria.

[function-field.ts](function-field.ts) initializes one mutable field on a fresh
arrow, writes through the original reference and reads/calls through an alias.
Both producers verify it. Explicit `Object.assign` type arguments are required:
SKJS currently infers `never` without them. [function-field.mts](../function-field.mts)
checks independent rejection of corrupted field/signature contracts and source
annotations, report editing, and the intrinsic syntax restrictions. This does
not yet cover general field addition, multiple fields, or receiver behavior.

[receiver-call.ts](receiver-call.ts) brings `.call` on local arrows into the
pipeline, including an alias of a function with a field and a captured nullary
arrow. The receiver expression is evaluated before actuals even though its value
is ignored. [receiver-call.mts](../receiver-call.mts) distinguishes dropping that
effect, checks exact arity and receiver claims, and rejects targets whose inherited
intrinsic is not established by their source construction. Both producers verify
these examples; ordinary receiver-dependent methods remain outside the fragment.

Partial `.bind` is covered by the [incompleteness example](../skjs-incomplete/bound-arguments.ts):
SKJS rejects it, while tsc's claims independently verify. Its fixture notes live
with the [other incompleteness findings](../skjs-incomplete/README.md).
