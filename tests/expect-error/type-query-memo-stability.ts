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
