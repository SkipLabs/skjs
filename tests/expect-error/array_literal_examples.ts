// Basic array annotation and array operation refinement.
function numbersArray(): void {
  const numbers: number[] = [1, 2, 3, 4, 5];
  numbers.push(6);
  const first: number | undefined = numbers[0];
}

// Array literal refined to array via push and index access.
function arrayLiteralRefinement(): void {
  const values = [1, 2, 3];
  values.push(4);
  const first: number | undefined = values[0];
}

// Union target array refinement: Array<T> | null accepts a literal.
function unionArrayTarget(): void {
  const values = [1, 2, 3];
  takesArrayOrNull(values);
}

// Array literal passed directly to function with constrained generic T extends number[].
type NumberArray = number[];
type ArrayOrString = NumberArray | string;
function takesConstrainedArray<S extends ArrayOrString>(values: S): S {
  return values;
}

function constrainedArrayLiteralDirect(): void {
  const result = takesConstrainedArray([1, 2, 3]);
  const first = result[0];
  if (first !== undefined && first < 0) {
    return;
  }
}

// Tuple literal passed directly to function with constrained generic T extends tuple | something.
type NumberPair = [number, number];
type TupleOrString = NumberPair | string;
function takesConstrainedTuple<S extends TupleOrString>(values: S): S {
  return values;
}

function constrainedTupleLiteralDirect(): void {
  const result = takesConstrainedTuple([1, 2]);
  const first: number = result[0];
  if (first < 0) {
    return;
  }
}

// Helper for unionArrayTarget.
function takesArrayOrNull(values: number[] | null): void {
  if (values === null) return;
  values.push(4);
}

// Tuple refinement commits the literal, so array ops should fail.
function tupleThenArrayUse(): void {
  const values = [1, 2];
  takesTuple(values);
  // @skjs-expect-error This index key is not assignable to the index signature: expected number, got string
  values.push(3);
}

// Array refinement commits the literal, so tuple annotation should fail.
function arrayThenTupleUse(): void {
  const values = [1, 2];
  takesArray(values);
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const tuple: [number, number] = values;
}

// Tuple refinement should succeed for a matching tuple type.
function tupleRefinementOk(): void {
  const values = [1, 2];
  const tuple: [number, number] = values;
  if (tuple[0] < 0) {
    return;
  }
}

// Non-uniform tuple can be promoted to array of union type.
function promoteNonUniformTuple(): void {
  const values = [1, "a"];
  const arr: Array<number | string> = values;
  arr.push(2);
  arr.push("b");
}

// Non-uniform tuple indexing is accepted by SKJS but rejected by TS.
function nonUniformTupleIndexing(): void {
  const values = [1, "a"];
  const x: number = values[0];
  if (x < 0) {
    return;
  }
}

// Non-literal index access refines to array, then tuple annotation fails.
function indexRefinesArray(): void {
  const values = [1, 2];
  const idx: number = 1;
  const v = values[idx];
  if (v === undefined) {
    return;
  }
  if (v < 0) {
    return;
  }
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const tuple: [number, number] = values;
}

// Method access refines to array, then tuple annotation fails.
function methodRefinesArray(): void {
  const values = [1, 2];
  const mapped = values.map((x: number) => x + 1);
  const first = mapped[0];
  if (first === undefined) {
    return;
  }
  if (first < 0) {
    return;
  }
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const tuple: [number, number] = values;
}

// Tuple helper used by tupleThenArrayUse and tupleRefinementOk.
function takesTuple(values: [number, number]): void {
  if (values[0] < 0) {
    return;
  }
}

// Literal tuple helper used by literalPrecisionLoss.
function takesLiteralTuple(values: [1, 2]): void {
  if (values[0] < 0) {
    return;
  }
}

// Array helper used by arrayThenTupleUse and unionArrayTarget.
function takesArray(values: number[]): void {
  values.push(3);
}

// --- Empty Array Literal Tests ---

// Empty array literal with annotation refines to the annotated type.
function emptyArrayWithAnnotation(): void {
  const arr: number[] = [];
  arr.push(1);
  arr.push(2);
  const first: number | undefined = arr[0];
  if (first !== undefined && first < 0) {
    return;
  }
}

// Empty array literal without annotation refines to Array<T> for fresh T.
function emptyArrayNoAnnotation(): void {
  const arr = [];
  arr.push(1);
}

// --- Supertype Position Test (RHS TArrayLit) ---

// When a generic function receives two array literals, the first constrains T
// and the second must be compatible. This exercises the RHS TArrayLit case
// when the type variable T carries the first literal's type.
function genericMerge<T>(a: T, b: T): T {
  return a;
}

function supertypePositionTest(): void {
  // Both literals refine through T; the second checks against T's constraint
  const result = genericMerge([1, 2], [3, 4, 5]);
  // Result should be compatible with array operations
  const first = result[0];
  if (first < 0) {
    return;
  }
}

// Both `takesTuple(numbers)` calls correctly fail and `takesArray(numbers)`
// correctly succeeds, matching TypeScript. Before the TupleN-via-TObject flip
// this test passed both `takesTuple` calls and rejected `takesArray` —
// arity-5 was silently accepted as `[number, number]` because tuples were
// modelled as a homogenous-element shape and treated as not-quite-an-array.
// Tuples are now structural classes that extend ReadonlyArray, so:
//   - `[1,2,3,4,5]` cannot be a `[number, number]` (arity mismatch)
//   - but it IS an `Array<number>` once committed
//   - and once committed to Array, it can't be re-committed to a tuple
// Each of those three behaviours is what `tsc` produces too.
function tupleThenArrayUse2(): void {
  const numbers = [1, 2, 3, 4, 5];
  // @skjs-expect-error Argument is not assignable to the parameter's type
  takesTuple(numbers);
  takesArray(numbers);
  // @skjs-expect-error Argument is not assignable to the parameter's type
  takesTuple(numbers);
}

// Precision loss example: committing a widened tuple can reject literal usage.
function literalPrecisionLoss(): void {
  const values = [1, 2];
  takesLiteralTuple(values);
  takesLiteralTuple(values);
}

// Array literal commits to annotated type, not narrower inferred type.
type UnionWithObject = string | number | { x: number };
function arrayWithObjectUnion(): void {
  const arr: UnionWithObject[] = ["a", 1];
  arr[0] = { x: 42 }; // Would fail if arr inferred as Array<string | number>
}

// Uncommitted literal adopts wider type from first constrained use.
function arrayCommittedTypeTest(): void {
  const arr = ["a", 1];
  const arr2: UnionWithObject[] = arr; // Commits arr to Array<UnionWithObject>
  arr[0] = { x: 42 }; // Proves arr has the wider type
}

// --- ReadonlyArray Commitment Tests ---

// Array literal commits to Array<T> which is a subtype of ReadonlyArray<T>.
function arrayLiteralAsReadonly(): readonly number[] {
  return [1, 2, 3];
}

// Array literal assigned to a readonly-annotated variable.
function arrayLiteralReadonlyAnnotation(): void {
  const xs: readonly number[] = [1, 2, 3];
  const first: number | undefined = xs[0];
}

// Array literal passed as argument to readonly parameter.
function takesReadonly(xs: readonly number[]): readonly number[] {
  return xs;
}
function arrayLiteralReadonlyArg(): readonly number[] {
  return takesReadonly([1, 2, 3]);
}

numbersArray();
arrayLiteralRefinement();
unionArrayTarget();
arrayWithObjectUnion();
constrainedArrayLiteralDirect();
constrainedTupleLiteralDirect();
tupleThenArrayUse();
arrayThenTupleUse();
tupleRefinementOk();
promoteNonUniformTuple();
nonUniformTupleIndexing();
indexRefinesArray();
methodRefinesArray();
emptyArrayWithAnnotation();
emptyArrayNoAnnotation();
supertypePositionTest();
literalPrecisionLoss();
arrayCommittedTypeTest();
