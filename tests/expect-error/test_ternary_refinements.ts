// Tests for type refinements in ternary operators

function testIfElseRefinement(x: string | null): string {
  // This works with if/then/else - type refinements are applied
  if (x !== null) {
    return x.toUpperCase(); // x is refined to string here
  } else {
    return "default";
  }
}

function testTernaryRefinement(x: string | null): string {
  return x !== null ? x.toUpperCase() : "default";
}

function testNestedTernary(x: string | null, y: number | null): string {
  // Test nested ternary with multiple refinements
  return x !== null
    ? y !== null
      ? x.toUpperCase() + y.toString()
      : x.toUpperCase()
    : "default";
}

function testTernaryWithTypeOf(value: string | number): string {
  // Test typeof refinements in ternary operators
  return typeof value === "string"
    ? value.toUpperCase()
    : (value + 1).toString();
}

function testTernaryWithInstanceOf(obj: Array<string> | string): number {
  // Test instanceof refinements in ternary operators
  return obj instanceof Array ? obj.length : obj.length;
}

// Test ADT (Algebraic Data Type) refinement with ternary
type Response =
  | { kind: "success"; data: string }
  | { kind: "error"; message: string };

function testTernaryWithADT(response: Response): string {
  // Test ADT refinement in ternary operators
  return response.kind === "success" ? response.data : response.message;
}

function branchWriteInvalidatesEarlierNarrowing(flag: boolean): number {
  let state: number | null = 1;
  state = 1;
  const result = flag ? (state = null) : 0;
  // @ts-expect-error Type of returned value is not assignable to the function's return type
  return state;
}

function bothBranchesInitialize(flag: boolean): number {
  let state: number;
  const result = flag ? (state = 1) : (state = 2);
  return state;
}

function oneBranchDoesNotInitialize(flag: boolean): number {
  let state: number;
  const result = flag ? (state = 1) : 0;
  // @ts-expect-error Variable 'state' is used before being assigned
  return state;
}
