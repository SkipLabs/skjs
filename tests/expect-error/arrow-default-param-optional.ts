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
// FIXME: SKJS resolves the global instead of the later nested parameter.
function laterNestedParameterDefault(
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
// FIXME: SKJS resolves the global instead of the later array rest binding.
function laterRestParameterDefault(
  result: number = restDefaultValue.length,
  [...restDefaultValue]: number[] = [],
): number {
  return result;
}
