# Source fragment boundary

The source fragment is the subset of TypeScript admitted by the parser and
source elaborator. The tables distinguish restrictions required by the
specified semantics from limits of the supported translation. A refusal
establishes that this pipeline cannot verify that source under its current
rules; it does not establish that the program is unsafe.
[Source contracts](SOURCE-CONTRACTS.md) gives the interpretation of annotations
and external declarations; [the trust surface](DESIGN.md#trust-surface) states
the assumptions used when connecting the extracted graph to JavaScript.

## Fragment boundary

What the pipeline refuses, each with its reason, in the two classes the
coverage run counts (`CLASSES` in
[skjs-coverage.mts](pipeline/skjs-coverage.mts),
[refusal classes](pipeline/SKJS-COVERAGE.md#method)). A refusal is
**principled** only when the construct is unsound, not faithful to
JavaScript, rejected by TypeScript, or safe only under an assumption the
project declines; any other refusal is a **model limit**, a gap, with the
obstacle named. A search failure is neither.

### Refused on principle

| Construct | Refused because |
| --- | --- |
| `new Array(n)`, `new Array(x)` with one argument | A numeric argument constructs holes; a readable element contract excluding `undefined` cannot justify those reads. The source gate refuses the ambiguous one-argument form. |
| An element write at an index not proven in bounds or appending | It could create a hole. |
| A mutable `Dog[]` as an `Animal[]`, a mutable dictionary of `true` as one of `boolean`, a readonly view as a writable one | Mutable storage is invariant: a write through the wider alias breaks the narrower one's contract (TypeScript's covariance is unsound). |
| Method bivariance (`Handler<Dog>` as `Handler<Animal>`), an override with narrower parameters, a narrower constructor at a construct signature | The member may be invoked with the wider argument. |
| A method as a function-typed property, method extraction (`o.m.call(r)`, `.apply` and `.bind` of one included), a write to a method member; a function whose `this` is typed where a receiver-indifferent callback is expected | A method is host-relative: read off its host it loses its receiver, and TypeScript's typing of it is unsound. |
| A record type where an index signature or a dictionary is expected (TypeScript's implicit index signature); width subtyping into an optional field; an array where a number index is expected | A record is open: it may own further keys at any type; an array has a prototype a dictionary lacks. |
| A position past a mutable tuple's arity; its `length` read at the arity | `push` may have extended it: TypeScript's `undefined` there, and its literal length, are unsound. |
| Narrowing `unknown` by `instanceof C`, and a member read of the result | JavaScript gives an object `C`'s prototype without `C`'s constructor running (`Object.create(C.prototype)`, `Object.setPrototypeOf`, `Reflect.construct` with `C` as the new target), so "an object whose chain holds `C`'s prototype has `C`'s fields" is false of values a unit may receive. |
| `instanceof` of a constructor not declared at the file's top level (imported, ambient, a function, an expression) | Nothing in the file says which prototype it gives its instances; trusting it is an assumption declined. |
| A base class declared later, imported, ambient, or an expression | Nothing in the file says what its constructor allocates (TypeScript rejects the first). |
| `key in o` on an operand with a primitive arm or `unknown` | JavaScript throws on a primitive, and TypeScript rejects both. |
| A loop or an array pattern over an iterable whose iterator's type states no `return` | Leaving it early, or a throw out of its body, calls whatever `return` the iterator owns, and an open record type says nothing of that property. |
| Async return or non-promise `await` without a stable non-thenable contract | JavaScript adopts thenables. Ordinary arrays and lifetime primitive-valued or absent `then` contracts establish the supported bound; an arbitrary record type does not. |
| An object literal, class or parameter property the source builds with a `then` member, which could be claimed as a `Promise` | A value of type `Promise<T>` is assumed a realm promise; the source must not forge one. |
| A write replacing a native promise's `constructor` or declared prototype members through any structural alias; an own `then` on an ordinary array | These violate the [native promise and stable non-thenable contracts](SOURCE-CONTRACTS.md#async-functions-and-await), including their requirements on external inputs. |
| A source declaration merged with the standard `Promise` interface | Native factories produce standard promises. Extra fields or overloads in a declaration do not establish that the returned values meet them. |
| An async return annotated with a nested promise when fresh resolution yields a non-promise payload | `Promise<A>` states the fulfillment value's type. The [async return rule](SOURCE-CONTRACTS.md#async-functions-and-await) checks the freshly resolved promise against that annotation; a number payload does not meet a promise payload contract. |
| `catch` or `finally` promising to preserve an open record payload without restricting its `then` | The fresh result resolves that payload again, which can adopt a callable `then` and change the fulfillment value. |
| A `finally` callback returning an open record without a stable non-thenable contract | Resolving the cleanup result invokes a hidden `then`, whose arguments and effects the record contract does not constrain. A native cleanup promise has a separate identity contract. |
| `String(o)`, `o + ""`, `new Date(o)`, `new Set(it)` of a non-array iterable, `JSON.parse` with a reviver, `JSON.stringify` with a replacer, of an array or an open record; a relational comparison with an object operand | The host runs client code (`toString`, `valueOf`, an iterator, a callback, a `toJSON`). |
| `+` on a bigint, number–bigint arithmetic, a symbol in a concatenation; a relational comparison of a string with a number | TypeScript refuses these operations. |
| `==` or `!=` that may convert an object to a primitive, including an array | Conversion may invoke client hooks and mutate aliases. Standard array string conversion does not justify default-hint conversion, which calls `valueOf` first. TypeScript reports an array compared with a primitive as having no overlap, so only a union reaches the conversion: too rare to justify a `valueOf` restriction and a runtime array dispatch ([utility](DESIGN.md#principles)). |
| `this` before `super(...)` | TypeScript rejects it, and JavaScript throws. |
| A read of a local above its declaration or in its own initializer; a parameter default reading a later parameter | JavaScript throws there (the temporal dead zone), and TypeScript rejects it (TS2448, TS2373). |
| An assignment to a module function's binding | TypeScript rejects it (TS2630). |
| A call of a `Function` value | It states no signature to call it at: TypeScript calls it at `any`, which states no contract. |
| A fresh callable given a field `call`, `bind`, `name`, `length`, `caller` or `arguments` (`Object.assign(f, { name })`) | An own `call` or `bind` would replace the intrinsic the parser identifies by lexical provenance ([trust surface](DESIGN.md#trust-surface)); a function owns `name` and `length` unwritable and inherits `caller` and `arguments` as accessors that throw, so JavaScript's copy throws where TypeScript types the callable with the field. |
| A class extending `Array` | Its instances' `constructor` is the subclass, so `map`, `filter` and `slice` construct their results through it (`ArraySpeciesCreate`), which [ordinary array construction](SOURCE-MODEL.md#arrays) excludes (`invalid-array-subclass`). |
| A catch binding annotated other than `unknown`, or destructured | Anything may be thrown; TypeScript's alternative is `any`. |
| TypeScript's `any` in the checked module's own annotations; a contextual closure parameter TypeScript types `any` | It states no contract. |
| A rest parameter typed by what is no array | TypeScript rejects it (TS2370). |
| A rest parameter typed by an intersection (`...xs: T[] & (number[] \| string[])`) | Its declared contract can be empty at an instance TypeScript admits: at `T := boolean` no array is both a writable `boolean[]` and a `number[]`, writable storage being invariant, yet TypeScript accepts `f<boolean>()`, and a body writing through one operand's view returns a number as a `boolean` (`invalid-rest-intersection`, executed under Node by `test.mts`). |
| A type that normalizes to nothing as a whole (`string & { a: number }`, `(() => void) & number[]`, `number[] & { map: number }`); as an arm of a union such an intersection adds nothing | No value of the model inhabits it (TypeScript keeps a branded primitive); it is refused rather than verified vacuously. |
| An empty module (no function, no initialization code) | Accepting it would check nothing. |

### Model limits

Sound JavaScript that TypeScript accepts, refused because the model or its
representation cannot state it yet; the paths are in
[next steps](WORK.md#next-steps).

| Construct | Obstacle |
| --- | --- |
| `catch` or `finally` after a void async completion, through a `Promise<void>` annotation | That completion fulfills with `undefined`, but `void` denotes `unknown` and the annotation loses this evidence. An arbitrary `Promise<unknown>` payload can contain a hidden callable `then`, so discarding the result alone cannot justify re-resolution. |
| A write adding a key (`o.x = 5` where `o`'s type does not state `x`, a writable optional field, a key of an index) to an object another reference may hold: a parameter, a module constant, a local whose object was passed, stored, captured, returned, copied to another binding or written into itself, or a write in a loop the declaration does not enclose | The model's objects keep their keys, and a key is added by copying the object: another reference would still see the object without the key, where JavaScript's sees it with. |
| A write at a string key known only at run time (`d[k] = v`), even on a local's own dictionary | The string may spell a key the model keeps for itself (`[]`, `[[proto]]`), which JavaScript owns as an ordinary property. |
| A write of `__proto__`; adding a symbol key | The first runs the prototype's setter and adds no key; the copy that adds a key copies string keys only. |
| `Object.assign` onto an object other than a fresh literal or, as a statement, a local's own object; from a source whose type does not rule out an own `__proto__` | Its value is its target, and another reference would see the keys it adds; it sets `__proto__` through the prototype's setter, which replaces the prototype. |
| `===` or `!==` between two operands neither known to be a primitive or an object (`unknown`, a type parameter's value); narrowing by object identity | Two such values may be of no kind the operator decides; a statement entry states no slot equality. |
| A relational comparison converting a primitive (`undefined`, a Boolean) | The model's comparison is of two numbers or two strings; the refusal does not tell this conversion, which runs no code, from an object's. |
| `keyof T`, `T[K]` over a function's own type parameter (an alias computed from its parameters is evaluated at each application) | They are functions of the type an instance names (its declared, optional and readonly keys); a parameter row denotes a value set, which does not determine a key set. |
| A template literal type with a `${string}` hole; `keyof` with a unique-symbol key; `typeof` of a binding whose inferred type is not an object literal's record of literals and primitives, or of a class with statics | No term of the fragment states it exactly. |
| An intersection with a union holding a type parameter, `(T \| null) & A`; a function type met with a record of readonly or optional fields, methods or an index | It distributes into meets known only at an instance; no clause states such a callable. |
| `declare let`, `declare var`, a module-level `let` or `var` | A unit's module inputs are immutable slots; module storage needs cells every call may write. |
| An ambient `declare enum`; an enum member TypeScript computes no value for; a NaN or infinite member; a reverse key naming a member; an empty enum | An enum type is its value set, which an ambient declaration need not state; the other keys are known only at run time, or have no literal type, or leave no record. |
| A `this` read in sloppy code | The receiver rule is strict code's; sloppy receiver conversion (the global object, a wrapper) has no term. |
| A library class other than `Array` as a base (`extends Map`) | Construction allocates an ordinary object at the class's fields; a library constructor's instance has no construction rule. |
| `key in o` for a string literal key the realm's prototypes hold (another key is the host's `%HasProperty%`, a Boolean narrowing nothing); a class value as the operand of `in`; `key in x` on an `unknown` a `typeof` test found an object (`typeof x === "object" && x !== null`) | The model holds no key of the realm's prototypes and would answer otherwise than JavaScript; a class's statics are bound apart; a `typeof` test answering `"object"` gives `unknown` no narrower type, and `in` needs an operand of object types, as it throws on a primitive. |
| A user-defined type guard (`x is T`) or assertion function (`asserts x is T`), with a body or declared | Its promise relates the result, or the completion, to the argument, which no function type states. |
| An array assignment pattern writing a field (`[o.f] = e`) | Its target's reference is evaluated before its position is read and defaulted; the lowering writes locals only. |
| An accessor (`get`/`set`), `__proto__`, a computed key in a literal other than a `unique symbol` constant, a spread of a string or of a value that may be a class | The heap has data properties only; the key or copy is known only at run time (a string's characters); a class's static fields are bindings of the model, not properties of the class value a copy reads. |
| A literal or class member keyed by a well-known symbol other than `Symbol.iterator` (`Symbol.toStringTag`, `Symbol.toPrimitive`, …), but a class's static `[Symbol.hasInstance]` method, which `instanceof` calls | It changes how the host treats the object, which the model does not state; a tag would let it pass for a host collection, whose iteration is trusted. |
| An element read past a readonly tuple arm's length (`const [a, b] = t` with `t: readonly [number] \| readonly [number, string]`) | No element rule reads `undefined` beyond an exact length. |
| A rest parameter of a definition typed by a type parameter; one typed by a tuple with optional or rest elements | A definition has no allocation rule for an array only an instance fixes (a function type's is a pack); several lengths are several signatures. |
| A written `let` pattern in a `for` head, or a written `let` in a `for...of` head; a test of a written `let` holding a union of objects; a `let` captured by a closure in a `for` loop | Its bindings are cells, which only a statement of a block lowers them to; a cell's known contents are primitive or merely no `undefined`; JavaScript copies the binding per iteration, which the lowering does not. |
| An array pattern over a value that may not be an array | The pattern reads an array's positions; over a host non-array iterable it would step `%Iterate:K%`, which the lowering does not place. |
| A generic or optional method declaring `this: T`; an optional method of a type literal nested in a declaration; a generic class method with a bounded binder; a constructor's rest parameter; a constructor parameter default, or a statement, reading `this` before the instance is complete | A generic method's member is a scheme its member bound to the host meets at every receiver, which states no type the host must meet, and an optional method is an optional field, whose function takes its declaration as receiver, which a nested literal is not; a generic class method's bounded binder, whose row its bound names; no rule constructs at a variadic construct signature; the instance is allocated at the end of the constructor. |
| A class member with a computed key other than a method's `unique symbol` constant or a static `[Symbol.hasInstance]`; an index signature in a class; a static block reading `this`; a class extending a generic class other than at the base's own binders | A method is a binding and a prototype key named by its plain name or its symbol; instances are what construction allocates; the block's receiver is the class value, whose statics are bindings of their own; a generic base's construction is at its binders' rows ([classes](SOURCE-CONTRACTS.md#classes)). |
| A class with a private name in inheritance; `#x in o` | A derived instance's base part is a copy, and a copy holds no private slot; the test asks for an own slot, where the model's key test walks the prototype chain. |
| An instance member or constructor reading a static of its own class; a static method that reads `this`; `super` in a static member; a mutable static field | Statics are bindings the class defines after its methods and constructor, whose closures cannot hold them, exact only when immutable; a static method's receiver is whatever its call passes, and its `super` the base's constructor. |
| `o.m?.()` | It would call the tested value with a receiver the lowering does not save. |
| A generator function (`function*`); `for await` | A body suspended at `yield` is no term of the calculus; an async iterator's steps are promises the model does not adopt. |
| An array literal spread (`[...xs]`) other than the one element over a program's or a host's iterable | No literal lowering takes a spread. |
| A library global both constructed and read through members, or both called and read through a method (`new Date()` beside `Date.now()`, `Symbol()` beside `Symbol.for`); an object type with construct signatures and other members | A class value or callable object with members has no clause. |
| Any library signature the overlays do not list (`Math.random`, `concat`) | Not reviewed; nothing is trusted by default. |
| A non-library global read other than through a member or a call (`const p = process`) | A global is assumed at the members and calls its references select; a read of the value selects none. |
| A module function without a result annotation | Its slot is its annotated signature, at which its unit is checked and every call reads it. |
| A mention, in a closure written above it, of a local that shadows an outer binding | JavaScript gives the name to the local from its block's start, and the closure reads it once it is initialized; the parser's renaming binds it from its declaration on ([shadowing](SOURCE-ELABORATION.md#derived-source-forms)). |
| A name declared in one `switch` clause and read in another | The clauses share one scope, where the lowering gives each clause's statements a scope of their own; a read reached by falling through, or through a closure, finds the binding initialized. |
| A function declaration after a statement that always jumps | The lowering drops what follows a jump; the declaration is hoisted, so live code may name it. |
| An actual that runs code after a spread into an ordinary call's fixed parameters | The call reads a spread's elements once every actual is evaluated; the lowering copies a spread where it is written only into a rest. |
| A spread of a program's iterable after an operand that runs code; a default or a nested pattern in an array pattern over a program's iterable | The iterator is run before the statement, and a pattern's names are bound after its steps: the operand's or the default's code would run in another order than JavaScript's. |
| A call through a union of functions carrying fields | The producer claims a call through one arrow the actuals call, which such a union does not offer. |
| A constructor writing a field that has an initializer, or writing one field twice | The instance is allocated at the constructor's end, from one value per field. |
| A generic class's instance member or constructor reading its own class | The class value is quantified over its declaring unit's binders, which the unit reads as parameter rows, and a module value is read only at ground instances. |
| An unannotated `let` of `null`, `undefined` or `[]` whose writes grow with it (`r = { tail: r }`) | Its contract is the union of what is written into it, which has no fixed point there. |
| A `let` with neither an initializer nor an annotation (`let y;`) | TypeScript types it as an evolving `any`; the pipeline reads a local's contract from its annotation or its initializer, and infers none from its later writes. |
| An imported interface its module declares more than once | The declaration reader resolves an import to one declaration; the merge of an interface declared twice is read for the checked file's own declarations ([interface merging](PROGRAM-TYPING.md)). |
| A closure parameter without an annotation that TypeScript types by an object type written nowhere by name | The parameter's annotation is TypeScript's contextual type, which the parser writes only through primitives, literals, arrays, type parameters and declarations by name. |
| A read through a field holding an object beside `null`, after a guard found the object (`x.child !== null`, then `x.child.b`) | What a location is known to hold is a union of primitives or its contract less `undefined` ([current contents](SOURCE-MODEL.md#current-content-assertions)): the guard states nothing of the object. |
| `unknown` used as an array after `Array.isArray` or `instanceof Array` | The array invariant is stated of record and dictionary members; `unknown`, which a handler binds a thrown value at, carries none ([next steps](WORK.md#next-steps)). |
| `Object.assign` onto an array | The copy takes the target's fields but its store, so its result would be no array. |
| `\|\|=` or `&&=` on a target other than a Boolean | The lowering tests the value read as a Boolean. |
| A source key spelling one the model keeps for itself (`"[]"`, a name in double brackets) | The model holds an array's store and an object's prototype under those keys: an object owning one would be read otherwise than JavaScript reads it. |

