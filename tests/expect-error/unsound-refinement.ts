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

// FIXME: tsc rejects destructuring an alias into a permanently narrow binding.
function destructuredAlias(x: { f: number | null }): number {
  let y: { readonly f: number } = { f: 0 };
  if (x.f !== null) {
    [y] = [x];
    x.f = null;
    return y.f;
  }
  return 0;
}

// Readonly tuple slots do not freeze the objects stored in them.
// FIXME: tsc rejects the stale read, even though the tuple is created narrowed.
function readonlyTupleAlias(x: { f: number | null }): number {
  if (x.f !== null) {
    let saved = [x] as const;
    x.f = null;
    return saved[0].f;
  }
  return 0;
}

// Defaults bypass literal element typing and need their own stable contract.
// FIXME: tsc rejects the narrow binding populated by this default.
function defaultAlias(x: { f: number | null }, missing: [undefined]): number {
  let y: { readonly f: number } = { f: 0 };
  if (x.f !== null) {
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
