// Destructuring a key that does not exist on the source: the 2339 error is
// correct, and the "unreachable default" warning is FALSE — the key is
// absent, so the default is the ONLY thing that fires at runtime (#799).
function missingKeyDefault(x: { a: number }): void {
  // @skjs-expect-error Property 'b' does not exist on this type
  const { b = 3 } = x;
}

function uselessDefault(x: { f: number }): number {
  // @skjs-expect-warning This default is unreachable because the field cannot be 'undefined'
  const { f = 1 } = x;
  return f;
}

function uselessDefaultNull(x: { f: null }): void {
  // @skjs-expect-warning This default is unreachable because the field cannot be 'undefined'
  const { f = 1 } = x;
}

function uselessDefaultUnion(x: { f: number } | { f: string }): void {
  // @skjs-expect-warning This default is unreachable because the field cannot be 'undefined'
  const { f = true } = x;
}

function usefulDefault(
  x: { f: number } | { f?: string },
): number | string | boolean {
  const { f = true } = x;
  return f;
}

function defaultSameType(x: { f?: number }): number {
  const { f = 1 } = x;
  return f;
}

function defaultSameType2(x: { f: number | undefined }): number {
  const { f = 1 } = x;
  return f;
}

function defaultOtherType(x: { f?: number }): number | string {
  const { f = "a" } = x;
  return f;
}

function defaultOtherType2(x: { f: number | undefined }): number | string {
  const { f = "a" } = x;
  return f;
}

function defaultUndefined(x: { f?: number }): number {
  const { f = undefined } = x;
  return f ?? 0;
}

function defaultUndefined2(x: { f: number | undefined }): number {
  const { f = undefined } = x;
  return f ?? 0;
}

function optionalMeansUndefined(x: { f?: number }): number {
  const { f } = x;
  return f ?? 0;
}

function optionalMeansUndefinedWitness(x: { f: number }): number {
  const { f } = x;
  // @skjs-expect-warning This operator has no effect; the operand is never null or undefined
  return f ?? 0;
}

function skippedDefaultKeepsPreviousValue(seed: number | undefined): number {
  let state: number | null = null;
  const { value = (state = 1) } = { value: seed };
  // @ts-expect-error Type of returned value is not assignable to the function's return type
  return state;
}

function skippedDefaultDoesNotInitialize(seed: number | undefined): number {
  let state: number;
  const { value = (state = 1) } = { value: seed };
  // @ts-expect-error Variable 'state' is used before being assigned
  return state;
}

function defaultCanInvalidatePreviousValue(seed: number | undefined): number {
  let state: number | null = 1;
  const { value = (state = null) } = { value: seed };
  // Discarding default effects entirely would lose this null write.
  // @ts-expect-error Type of returned value is not assignable to the function's return type
  return state;
}

function checkedStateAfterDefault(seed: number | undefined): number {
  let state: number | null = null;
  const { value = (state = 1) } = { value: seed };
  return state ?? 0;
}

function skippedAssignmentDefaultKeepsPreviousValue(
  seed: number | undefined,
): number {
  let state: number | null = null;
  let value: number | undefined = 0;
  [value = (state = 1)] = [seed];
  // tsc accepts this, but supplying seed leaves state null.
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return state;
}

function inferredFieldDefault(seed: number | undefined): number {
  const box = { value: seed };
  const { value = 0 } = box;
  return value;
}
function inferredIterableDefault(seed: number | undefined): number {
  const values = [seed];
  const [value = 0] = values;
  return value;
}
function inferredAssignmentDefault(seed: number | undefined): number {
  const values = [seed];
  let value: number = 0;
  [value = 0] = values;
  return value;
}
function inferredDefaultKeepsNull(seed: number | null | undefined): number {
  const box = { value: seed };
  const { value = 0 } = box;
  // @ts-expect-error Type of returned value is not assignable to the function's return type
  return value;
}
function inferredDefaultCanReturnUndefined(seed: number | undefined): number {
  const box = { value: seed };
  const { value = undefined } = box;
  // @ts-expect-error Type of returned value is not assignable to the function's return type
  return value;
}

function laterPatternRead(x: { a?: null; b: number | null }): number {
  if (x.b !== null) {
    const { a = (x.b = null), b } = x;
    // @ts-expect-error Type of returned value is not assignable to the function's return type
    return b;
  }
  return 0;
}
// Reading b before the default takes a scalar snapshot. TypeScript
// conservatively rejects its return, but the later write cannot change it.
function earlierPatternRead(x: { a?: null; b: number | null }): number {
  if (x.b !== null) {
    const { b, a = (x.b = null) } = x;
    return b;
  }
  return 0;
}

function checkedNestedPattern(x: {
  child: { a?: number; b: number } | null;
}): number {
  if (x.child !== null) {
    const {
      child: { a = 0, b },
    } = x;
    return a + b;
  }
  return 0;
}
function nestedPatternWithNull(x: {
  child: { a?: number; b: number } | null;
}): number {
  const {
    // @ts-expect-error Cannot use object-destructuring on this type
    child: { a = 0, b },
  } = x;
  return a + b;
}

const later: number = 1;
function patternLaterBinding(source: {
  first?: number;
  later?: number;
}): number {
  // @ts-expect-error Variable 'later' is used before being assigned
  const { first = later, later = 2 } = source;
  return first;
}
function patternEarlierBinding(source: {
  first?: number;
  later?: number;
}): number {
  const { later = 2, first = later } = source;
  return first;
}

function identityPatternAlias(
  x: { child: { value: number | null } },
  narrow: { value: number },
): number {
  if (x.child !== narrow) return 0;
  const { child } = x;
  x.child.value = null;
  // @ts-expect-error Type of returned value is not assignable to the function's return type
  return child.value;
}

// The nested pattern copies a scalar before the write. TypeScript
// conservatively rejects this return, but no object alias escapes the pattern.
function identityPatternScalar(
  x: { child: { value: number | null } },
  narrow: { value: number },
): number {
  if (x.child !== narrow) return 0;
  const {
    child: { value },
  } = x;
  x.child.value = null;
  return value;
}
