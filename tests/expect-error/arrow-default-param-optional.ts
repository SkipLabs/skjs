// A default value makes a parameter optional at the call site, so a
// function with a defaulted parameter should be assignable to a function
// type whose parameter is optional (`x?`). tsc --strict accepts both the
// named and the arrow forms below.

function namedDefaultParam(x: number = 0): number {
  return x;
}

function assignNamed(): void {
  const g: (x?: number) => number = namedDefaultParam;
}

function assignArrow(): void {
  const f = (x: number = 0): number => x;
  const g: (x?: number) => number = f;
}

// A later default must see the earlier parameter's rigid generic type.
function earlierGenericDefault<T>(value: T, result: T = value): T {
  return result;
}

// An earlier defaulted parameter is available when a later default runs.
function earlierArrowDefault(): number {
  const read = (value: string = "ready", text: string = value): number =>
    text.length;
  return read();
}

// Passing first skips its initializer, so its assignment cannot justify the
// second default's non-null promise.
function skippedEarlierDefault(
  value: string | null,
  first: string = (value = "ready"),
  // @ts-expect-error Type of default value is not assignable to the parameter's type
  second: string = value,
): string {
  return second;
}

// A parameter is unavailable during its own initializer.
// @ts-expect-error Variable 'value' is used before being assigned
function selfReferentialDefault(value: number = value): number {
  return value;
}

// A later parameter shadows this top-level name before it is
// initialized; resolving the top-level value hides a runtime ReferenceError.
const nextDefaultValue: number = 1;
function laterParameterDefault(
  // @ts-expect-error Variable 'nextDefaultValue' is used before being assigned
  result: number = nextDefaultValue,
  nextDefaultValue: number = 2,
): number {
  return result;
}

const nestedDefaultValue: number = 1;
// Nested bindings shadow globals throughout the parameter list.
function laterNestedParameterDefault(
  // @ts-expect-error Variable 'nestedDefaultValue' is used before being assigned
  result: number = nestedDefaultValue,
  {
    values: { nestedDefaultValue },
  }: { values: { nestedDefaultValue: number } } = {
    values: { nestedDefaultValue: 2 },
  },
): number {
  return result;
}

const restDefaultValue: string = "outer";
// Rest bindings participate in the same temporal dead zone.
function laterRestParameterDefault(
  // @ts-expect-error Variable 'restDefaultValue' is used before being assigned
  result: number = restDefaultValue.length,
  [...restDefaultValue]: number[] = [],
): number {
  return result;
}

// An extracted generic retains its rigidity in later defaults.
function extractedGeneric<T>({ value }: { value: T }, result: T = value): T {
  return result;
}

// Pattern defaults can depend on earlier fields in the same pattern.
function siblingDefaults({
  first = "ready",
  second = first,
}: {
  first?: string;
  second?: string;
}): string {
  return second;
}

// Supplying first skips the write, so value may still be null.
function skippedPatternDefault(
  value: string | null,
  { first = (value = "ready") }: { first?: string },
): string {
  // @ts-expect-error Type of returned value is not assignable to the function's return type
  return value;
}

const laterPatternValue: number = 1;
// A later pattern binding shadows the global during field defaults.
function patternTdz({
  // @ts-expect-error Variable 'laterPatternValue' is used before being assigned
  first = laterPatternValue,
  laterPatternValue,
}: {
  first?: number;
  laterPatternValue: number;
}): number {
  return first;
}

// FIXME: A default replaces undefined, but preserves a supplied null.
function initializedDefault(
  value: string | null | undefined = "ready",
): string | null {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return value;
}

// A default that itself yields undefined provides no non-undefined guarantee.
function undefinedDefault(value: string | undefined = undefined): string {
  // @ts-expect-error Type of returned value is not assignable to the function's return type
  return value;
}

// Initialization does not shrink the declared write contract.
function reassignedDefault(value: string | undefined = "ready"): string {
  value = undefined;
  // @ts-expect-error Type of returned value is not assignable to the function's return type
  return value;
}

// A deferred read must account for writes after parameter initialization.
function capturedDefault(value: string | undefined = "ready"): () => string {
  // @skjs-expect-error Type of the callback's returned value is not assignable to the expected return type
  const read = (): string => value;
  value = undefined;
  return read;
}

// FIXME: Destructuring receives the value after the whole-parameter default.
function defaultObject(
  // @skjs-expect-error Cannot use object-destructuring on this type
  { value }: { value: string } | undefined = { value: "ready" },
): string {
  return value;
}
