// Query-stability controls: recursive relations, rigid parameters, repeated
// readonly views, incompatible later arguments, and inference. These outcomes
// must survive changes to cache policy; they do not prove cache validity.

type QuerySource<T> = {
  readonly next: QuerySource<T> | null;
  readonly value: T;
};

type QueryTarget<T> = {
  readonly next: QueryTarget<T> | null;
  readonly value: T;
};

// Different recursive aliases force structural comparison. The 'next' field
// is ordered before 'value', so recursive assumptions must remain local until
// the remaining scalar field has also been checked.
function queryRecursivePositive<T>(node: QuerySource<T>): QueryTarget<T> {
  return node;
}

function queryRecursiveMismatch(
  node: QuerySource<string>,
): QueryTarget<number> {
  // @ts-expect-error Type of returned value is not assignable to the function's return type
  return node;
}

function queryRigidParametersStayDistinct<T, U>(
  node: QuerySource<T>,
): QueryTarget<U> {
  // @ts-expect-error Type of returned value is not assignable to the function's return type
  return node;
}

class QueryCell<T> {
  value: T;
  constructor(value: T) {
    this.value = value;
  }
  set(value: T): void {
    this.value = value;
  }
}

function queryRepeatedReadonlyView(seed: number): number {
  const cell = new QueryCell(seed);
  const before: { readonly value: number } = cell;
  cell.set(seed + 1);
  const after: { readonly value: number } = cell;
  return before.value + after.value;
}

function queryLaterIncompatibleArgument(seed: number): void {
  const cell = new QueryCell(seed);
  const view: { readonly value: number } = cell;
  // @ts-expect-error Argument is not assignable to the parameter's type
  cell.set("wrong");
}

function queryCompoundIntersection(
  value: { readonly value: number } & { readonly tag: "ok" },
): { readonly value: number; readonly tag: "ok" } {
  return value;
}

function queryCompoundIntersectionMismatch(
  value: { readonly value: string } & { readonly tag: "ok" },
): { readonly value: number; readonly tag: "ok" } {
  // @ts-expect-error Type of returned value is not assignable to the function's return type
  return value;
}

declare function queryInfer<T>(value: T, same: (value: T) => T): T;

// The first check may infer a candidate. Refusing to memoize a mutating check
// must not refuse the check or prevent later inference from using its result.
function queryInferenceStillWorks(seed: number): number {
  return queryInfer(seed, (value: number): number => value);
}

function queryRecursiveArrayPositive(
  nodes: readonly QuerySource<number>[],
): readonly QueryTarget<number>[] {
  return nodes;
}

// A default decision reads the existing element type; it must not try to
// infer a different element type merely to decide whether undefined fits.
function queryFreshLiteralDefault(seed: number): number {
  // @skjs-expect-warning This default is unreachable because the element cannot be 'undefined'
  const [value = 0] = [seed];
  return value;
}
// Structural validation must commit the literal representation before a
// length contract can escape through another view.
function queryLiteralLengthView(seed: number): 1 {
  const items = [seed];
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const view: { readonly length: 1 } = items;
  items.push(seed);
  return view.length;
}

// Both literal identities remain reachable through the conditional alias.
function queryConditionalLiteralLengthView(seed: number, pick: boolean): 1 {
  const first = [seed];
  const second = [seed + 1];
  const items = pick ? first : second;
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const view: { readonly length: 1 } = items;
  first.push(seed);
  second.push(seed);
  return view.length;
}

function queryLiteralBroadLengthView(seed: number): number {
  const items = [seed];
  const view: { readonly length: number } = items;
  items.push(seed);
  return view.length;
}

// FIXME: mixed await retains the literal's provisional tuple shape, losing
// the representation identity that the later push commits as an array.
async function queryMixedAwaitedLiteralLength(
  seed: number,
  pick: boolean,
  pending: Promise<number>,
): Promise<1> {
  const items = [seed];
  // @skjs-expect-warning 'await' can only be applied to a Promise
  const view = await (pick ? items : pending);
  if (typeof view === "number") return 1;
  items.push(seed);
  return view.length;
}

async function queryMixedAwaitedLiteralBroadLength(
  seed: number,
  pick: boolean,
  pending: Promise<number>,
): Promise<number> {
  const items = [seed];
  // @skjs-expect-warning 'await' can only be applied to a Promise
  const view = await (pick ? items : pending);
  if (typeof view === "number") return view;
  items.push(seed);
  return view.length;
}
