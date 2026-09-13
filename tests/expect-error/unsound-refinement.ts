// Mutation refinement regressions. Visible property writes invalidate known
// object refinements; effects hidden behind calls remain open.

declare function sideEffect(): void;

// 1. #597 — Field refined, then a side-effecting call happens between
// the test and the use. In a multithreaded context (or via a synchronous
// setter called inside `sideEffect`), `x.f` could have been reassigned.
function testFieldRefineThenSideEffect(x: { f: number | null }): void {
  if (x.f !== null) {
    sideEffect();
    const n: number = x.f;
  }
}

// 2. #598 — Field is reassigned to a wider value inside the refined
// branch. The setter typechecks (the field still accepts
// `number | null`), so the getter must lose its earlier narrowing.
function testFieldReassignInBranch(x: { f: number | null }): void {
  if (x.f !== null) {
    x.f = null;
    // @ts-expect-error Type of value is not assignable to the variable's type annotation
    const n: number = x.f;
  }
}

// 3. #599 — Local is captured by a lambda that reassigns it. The lambda
// is invoked inside the refined branch, so the narrowed type is stale
// when we use `x` afterwards.
function testLocalCapturedAndMutated(): void {
  let x: string | null = "hello";
  if (x !== null) {
    const reset = () => {
      x = null;
    };
    reset();
    const s: string = x;
  }
}

// Writes through an alias invalidate the source read fact; tsc accepts it.
function aliasBeforeNarrow(x: { f: number | null }): number {
  const y = x;
  if (x.f !== null) {
    y.f = null;
    // @skjs-expect-error Type of returned value is not assignable to the function's return type
    return x.f;
  }
  return 0;
}
// Readonly prohibits writes through this view, not other views; tsc accepts it.
function readonlyView(x: { f: number | null }): number {
  const y: { readonly f: number | null } = x;
  if (y.f !== null) {
    x.f = null;
    // @skjs-expect-error Type of returned value is not assignable to the function's return type
    return y.f;
  }
  return 0;
}
// Property writes preserve scalar snapshots and non-null reference facts;
// checking the field after the write establishes a fresh read fact.
function checkedAfterWrite(
  x: { f: number | null } | null,
  seed: number | null,
): number {
  if (x !== null && seed !== null) {
    const y = x;
    y.f = null;
    if (x.f !== null) return x.f;
    return seed;
  }
  return 0;
}
// Destructuring invalidates the same facts as plain writes.
function destructuredWrite(x: { f: number | null }): number {
  if (x.f !== null) {
    [x.f] = [null];
    // @ts-expect-error Type of returned value is not assignable to the function's return type
    return x.f;
  }
  return 0;
}

// A field check cannot establish a lasting alias contract while the original
// view can still write null.
function annotatedNarrowAlias(x: { f: number | null }): number {
  if (x.f !== null) {
    // @ts-expect-error Type of value is not assignable to the variable's type annotation
    const y: { f: number } = x;
    x.f = null;
    return y.f;
  }
  return 0;
}

// Readonly restricts writes through y, not writes through x.
function annotatedReadonlyAlias(x: { f: number | null }): number {
  if (x.f !== null) {
    // @ts-expect-error Type of value is not assignable to the variable's type annotation
    const y: { readonly f: number } = x;
    x.f = null;
    return y.f;
  }
  return 0;
}

// Stable contents and reference narrowing suffice for a lasting alias;
// the field value copied into a scalar also retains its current refinement.
function stableAnnotatedAlias(x: { f: number } | null): number {
  if (x !== null) {
    const y: { readonly f: number } = x;
    if (x.f === 1) {
      const snapshot: 1 = x.f;
      x.f = 2;
      return snapshot;
    }
    return y.f;
  }
  return 0;
}

// Initializing the alias earlier must not let a later assignment install a
// view invalidated by the source's writes.
function assignedNarrowAlias(x: { f: number | null }): number {
  let y: { readonly f: number } = { f: 0 };
  if (x.f !== null) {
    // @ts-expect-error Type is not assignable to the variable's type
    y = x;
    x.f = null;
    return y.f;
  }
  return 0;
}

// Reassignment can select a declared alternative and retain its stable fields.
function assignedUnionAlternative(
  x: { kind: "value"; f: number } | { kind: "empty" },
): number {
  let y: { readonly kind: "value"; readonly f: number } = {
    kind: "value",
    f: 0,
  };
  if (x.kind === "value") {
    y = x;
    x.f = 2;
  }
  return y.f;
}

// A narrowed source cannot satisfy a permanently narrow slot.
function storedNarrowAlias(
  x: { f: number | null },
  box: { item: { readonly f: number } },
): number {
  if (x.f !== null) {
    // @ts-expect-error Type is not assignable to the assignment target's type
    box.item = x;
    x.f = null;
    return box.item.f;
  }
  return 0;
}

// The inferred local slot can widen, but cannot retain an unsound narrow read.
function storedLocalAlias(x: { f: number | null }): number {
  const box = { item: { f: 0 } };
  if (x.f !== null) {
    box.item = x;
    x.f = null;
    // @skjs-expect-error Type of returned value is not assignable to the function's return type
    return box.item.f;
  }
  return 0;
}

// A new field inherits stable contents from an aliased value. A fresh scalar
// snapshot can be checked after mutation through the source.
// SKJS supports adding this field to {}; tsc requires declaring it upfront.
function grownAliasField(x: { f: number | null }): number {
  const box = {};
  if (x.f !== null) {
    box.item = x;
    x.f = null;
    const value: number | null = box.item.f;
    if (value !== null) return value;
  }
  return 0;
}

// Destructuring cannot install a permanently narrow alias from a field check.
function destructuredAlias(x: { f: number | null }): number {
  let y: { readonly f: number } = { f: 0 };
  if (x.f !== null) {
    // @ts-expect-error Type is not assignable to the variable's type
    [y] = [x];
    x.f = null;
    return y.f;
  }
  return 0;
}

// Readonly tuple slots do not freeze the objects stored in them.
function readonlyTupleAlias(x: { f: number | null }): number {
  if (x.f !== null) {
    let saved = [x] as const;
    x.f = null;
    // @ts-expect-error Type of returned value is not assignable to the function's return type
    return saved[0].f;
  }
  return 0;
}

// Defaults bypass literal element typing and need their own stable contract.
function defaultAlias(x: { f: number | null }, missing: [undefined]): number {
  let y: { readonly f: number } = { f: 0 };
  if (x.f !== null) {
    // @ts-expect-error Type is not assignable to the variable's type
    [y = x] = missing;
    x.f = null;
    return y.f;
  }
  return 0;
}

// Stable object contents and copied scalar facts survive array storage.
function checkedArrayAlias(x: { f: number } | null): number {
  if (x !== null && x.f === 1) {
    let saved = [x] as const;
    let [snapshot] = [x.f] as const;
    x.f = 2;
    const one: 1 = snapshot;
    return saved[0].f + one;
  }
  return 0;
}

// Defaults from tuple elements retain the source's nullable field.
function tupleDeclarationDefault(
  x: { f: number | null },
  input: [{ f: number } | undefined],
): number {
  if (x.f !== null) {
    const [y = x] = input;
    x.f = null;
    // @ts-expect-error Type of returned value is not assignable to the function's return type
    return y.f;
  }
  return 0;
}

// Iterable extraction follows a separate path from positional tuple binding.
// The default must not give an optional array element a stale guarantee.
function iterableDeclarationDefault(
  x: { f: number | null },
  input: { f: number }[],
): number {
  if (x.f !== null) {
    const [y = x] = input;
    x.f = null;
    // @ts-expect-error Type of returned value is not assignable to the function's return type
    return y.f;
  }
  return 0;
}

// Optional object fields have a separate default-binding path.
// The returned callback must handle writes through the default's source.
function objectDeclarationDefault(
  x: { f: number | null },
  input: { item?: { f: number } },
): () => number {
  if (x.f !== null) {
    const { item: y = x } = input;
    // @ts-expect-error Type of returned value is not assignable to the function's return type
    return () => y.f;
  }
  return () => 0;
}

function checkedDeclarationDefault(
  x: { f: number | null },
  input: { item?: { f: number } },
): number {
  if (x.f !== null) {
    const { item: y = x } = input;
    x.f = null;
    if (y.f !== null) return y.f;
  }
  return 0;
}

// A conditional's temporary field check cannot justify a lasting view.
function conditionalAnnotatedAlias(x: { f: number | null }): number {
  // @ts-expect-error Type of value is not assignable to the variable's type annotation
  const y: { readonly f: number } = x.f !== null ? x : { f: 0 };
  x.f = null;
  return y.f;
}

// Nested conditionals must compose contracts before their branch scopes end.
// An inferred alias must not export the transient type through a callback.
function nestedConditionalCapture(
  x: { f: number | null },
  choose: boolean,
): () => number {
  const y = choose ? (x.f !== null ? x : { f: 0 }) : { f: 0 };
  // @ts-expect-error Type of returned value is not assignable to the function's return type
  return () => y.f;
}

// Scalar selection and selecting an existing union alternative remain precise.
function checkedConditionalAlias(
  x: { kind: "value"; f: number } | { kind: "empty" },
): number {
  const y = x.kind === "value" ? x : { kind: "value", f: 0 };
  const snapshot = y.f === 1 ? y.f : 1;
  const one: 1 = snapshot;
  return y.f + one;
}

// Nullish selection carries a nested conditional's stable contract.
function nullishConditionalAlias(x: { f: number | null }): number {
  const y = (x.f !== null ? x : null) ?? { f: 0 };
  x.f = null;
  // @ts-expect-error Type of returned value is not assignable to the function's return type
  return y.f;
}

// An aliased fallback has a contract even when the first operand is safe.
function nullishFallbackAlias(
  x: { f: number | null },
  preferred: { f: number } | undefined,
): number {
  if (x.f !== null) {
    const y = preferred ?? x;
    x.f = null;
    // @ts-expect-error Type of returned value is not assignable to the function's return type
    return y.f;
  }
  return 0;
}

// Returning through a Promise does not stabilize an aliased object's fields.
async function asyncNarrowReturn(x: {
  f: number | null;
}): Promise<{ readonly f: number }> {
  // @ts-expect-error Type of returned value is not assignable to the function's return type
  if (x.f !== null) return x;
  return { f: 0 };
}

// An annotated expression body validates the stable branch contract.
function annotatedAliasReturn(): void {
  const select = (x: { f: number | null }): { readonly f: number } =>
    // @ts-expect-error Type of the callback's returned value is not assignable to the expected return type
    x.f !== null ? x : { f: 0 };
}

function inferredAliasReturn(): void {
  const select = (x: { f: number | null }) => (x.f !== null ? x : { f: 0 });
  // Inference must not export a temporary field fact as a result contract.
  // @ts-expect-error Type of value is not assignable to the variable's type annotation
  const narrow: (x: { f: number | null }) => { readonly f: number } = select;
}

// A freshly allocated result copies the checked scalar, rather than aliasing x.
async function freshReturnSnapshot(x: {
  f: number | null;
}): Promise<{ readonly f: number }> {
  if (x.f !== null) return { f: x.f };
  return { f: 0 };
}

// A direct assignment carries field-refinement provenance to its destination.
function assignedBroadAlias(x: { f: number | null }): number {
  let y: { f: number | null } = { f: 0 };
  if (x.f !== null) {
    y = x;
    x.f = null;
    // @skjs-expect-error Type of returned value is not assignable to the function's return type
    return y.f;
  }
  return 0;
}

function retainedArgument(
  x: { f: number | null },
  retain: (value: { readonly f: number }) => () => number,
): () => number {
  if (x.f !== null) {
    // A callee can retain an alias after the field check stops holding.
    // @ts-expect-error Argument is not assignable to the parameter's type
    const read = retain(x);
    x.f = null;
    return read;
  }
  return () => 0;
}

function genericArgument(
  x: { f: number | null },
  identity: <T>(value: T) => T,
): number {
  if (x.f !== null) {
    // Generic inference preserves the stable contract through T.
    const y = identity(x);
    x.f = null;
    // @ts-expect-error Type of returned value is not assignable to the function's return type
    return y.f;
  }
  return 0;
}

function snapshotArgument(
  x: { f: number | null },
  retain: (value: { readonly f: number }) => () => number,
): () => number {
  if (x.f !== null) {
    const read = retain({ f: x.f });
    x.f = null;
    return read;
  }
  return () => 0;
}
