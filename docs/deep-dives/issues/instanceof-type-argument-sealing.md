# Unsound: generic `instanceof` narrowing installs an empty inference argument

Proposed labels: `soundness`, `bug`, `narrowing`, `inference`.

## Finding

The true branch of `x instanceof C` establishes that the runtime value is an
instance of `C` at some type arguments within the class's declared bounds. In
the soundness model this is the existential instance type

```text
T_C^exists = union over U within the declared bounds of C<U>.
```

The implementation does not install that type. For a generic class it builds
`T_C = C<a>` with a fresh, unbound inference variable `a`. Canonical
`TVAR-SEM` gives an unbound variable the empty envelope. Consequently the
bridge required by registry row `L-INST`,

```text
sem(T_C^exists) is contained in sem(T_C),
```

is false: a runtime `C<number>` instance belongs to the existential type,
but for a class with a parameter-typed field it does not belong to `C<a>`
while `a` is unbound. The same instance witnesses the failure of `L-INST`
itself — a value the runtime predicate accepts is outside the installed
type — so `L-INST` fails when the branch type is installed, before the
branch body is checked.

The branch body turns this invalid installed type into an accepted program
with a runtime type error, in both data directions. A read: the first
covariant use binds the fresh variable from the expected type of that use.
A write: the check of the right-hand side against the unbound variable in a
parameter-typed field's set-type binds it instead of rejecting. In both
cases the program context chooses the type argument of an object that
already exists; no runtime value flow justifies the choice.

## Read-side witness (sealing)

Reproduction:
[`repros/instanceof-arg-sealing.ts`](repros/instanceof-arg-sealing.ts).
Run:

```sh
make check-file-in-docker \
  FILE=docs/deep-dives/issues/repros/instanceof-arg-sealing.ts \
  BIN=target/host/dev/skjs
```

The essential program is:

```ts
class Box<T> {
  v: T;
  constructor(v: T) {
    this.v = v;
  }
}

function h(x: unknown): string {
  if (x instanceof Box) {
    const s: string = x.v;
    return s;
  }
  return "no";
}

console.log(h(new Box(42)));
```

- SKJS accepts with no diagnostics and no use of `any`.
- At runtime `x` is a `Box<number>` and `x.v` is the number `42`.
- The expected type of `s` causes the unbound argument to be closed as
  `string`, so the checker accepts the read and the `string` return.
- Node prints `42`: a number has crossed a checked `string` boundary.

This directly falsifies type soundness at the corpus's capstone `L-TC`
(checked expressions inhabit their checked types): the accepted function is
declared to return `string`, but returns a number. It also demonstrates that
the failed `L-INST` bridge is operationally reachable rather than merely an
overly strong proof premise.

As a mechanism check, adding `const n: number = x.v` after the string read
makes SKJS reject and report the earlier read. The first expected type has
already closed the shared argument as `string`, confirming that contextual
use, rather than runtime evidence, selected the argument.

## Write-side witness (binding)

Reproduction:
[`repros/instanceof-arg-write-binding.ts`](repros/instanceof-arg-write-binding.ts).
Run:

```sh
make check-file-in-docker \
  FILE=docs/deep-dives/issues/repros/instanceof-arg-write-binding.ts \
  BIN=target/host/dev/skjs
```

With the same `Box`:

```ts
function w(a: Box<number>): number {
  const x: unknown = a;

  if (x instanceof Box) {
    x.v = "s"; // binds the fresh argument to string
  }

  return a.v;
}

console.log(w(new Box(1)));
```

- SKJS accepts with no diagnostics; Node prints `s` — the `number`-typed
  `w` returns a string, corrupting the sibling `Box<number>` view.
- Mechanism check: appending `const n: number = x.v` after the write makes
  SKJS reject with "Type string [the write's RHS] is not assignable to
  type number" — the write installed `string` as the argument. The first
  write wins, order-dependently, mirroring the read side.
- tsc (strict) also accepts, again via `Box<any>`.

Because the corrupted view is a sibling, the write side is also a
cross-view mutation-coherence violation (registry row `L-MUT-ALIAS`),
graded as the generic minted-view site by deep dive H.

## Implementation correspondence

- `evalInstanceof` constructs the narrowed object using `makeTArgs`
  (`src/TypeCheckRefine.sk`).
- `makeTArgs` creates one fresh candidate per class parameter and attaches
  its declared constraint (`src/TEnv.sk`).
- A covariant `grow` on an unbound candidate installs the expected type as an
  `SVClosed` binding (`src/TTypeSubst.sk`) — the read side.
- A write resolves the field's set-type to the unbound candidate
  (`src/TType.sk`, `TFields::resolveFieldType` with `isLValue`), and the
  right-hand-side check grows it instead of failing — the write side.

These operations implement ordinary inference variables. They do not
represent the fixed but hidden type arguments justified by the runtime
`instanceof` result.

The `instanceof Array` path is immune to this finding: `evalInstanceof`
special-cases `Array` to the closed argument `top`
(`src/TypeCheckRefine.sk`), so no unbound inference variable is installed.
(The separate `Array.isArray` narrowing intersects with
`ReadonlyArray<unknown>`.) The Array path has a distinct exposure of its
own — the installed view is the mutable `Array<top>`, so writes through it
are accepted at `top` — tracked as
[`instanceof-array-mutable-top-view.md`](instanceof-array-mutable-top-view.md).

## Sound repair shape

The precise representation is a rigid/existential witness whose identity is
fixed by the runtime object and cannot be bound by ordinary expected-type
propagation. The checker may expose safe observations of that hidden type,
but cannot manufacture values of it or redefine it from a use site.

Substituting `top` for every argument also discharges the `L-INST` bridge —
membership constrains values through get-types, which only weaken at `top` —
but it licenses branch-local writes and parameter-typed method calls at
`top` against an object whose actual argument is narrower, relocating the
exposure to mutation and calls; without a read-only or variance-aware view
it is not a sound repair. A conservative alternative is to suppress generic
`instanceof` narrowing, or to expose only class structure independent of the
hidden parameters.

## Corpus location

Deep dive A (`docs/deep-dives/runtime-grounding.tex`) owns `L-INST` and proves
the runtime containment into `T_C^exists` under its stated hypotheses
(`A-HASINST` — violated separately, see `symbol-hasinstance-narrowing.md` —
`A-PROTO`, and `L-TC` at construction sites). This finding refutes the
remaining bridge from `T_C^exists` to the fresh-`TVar` type installed by
`evalInstanceof`. Registry rows affected: `L-INST` (`violated`; the
installation failure and its read-side exposure) and `L-MUT-ALIAS`
(`violated`; the write-side exposure, one of deep dive H's minted-view
witnesses).

TypeScript also accepts the witness by narrowing to `Box<any>`, but that is a
separate, explicit `any` escape hatch. SKJS's counterexample is `any`-free and
depends on inference order.
