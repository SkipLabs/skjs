// Tests for type refinements in ternary operators
// This file demonstrates the current limitation and will test our fix

function testIfElseRefinement(x: string | null): string {
  // This works with if/then/else - type refinements are applied
  if (x !== null) {
    return x.toUpperCase(); // x is refined to string here
  } else {
    return "default";
  }
}

function testTernaryRefinement(x: string | null): string {
  // This should work with ternary operators after our fix
  // Currently this likely doesn't work due to missing type refinements
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
  return typeof value === "string" ? value.toUpperCase() : value.toString();
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

// Main function to run tests
function main(): void {
  console.log("Testing type refinements in ternary operators...");

  // Test basic null refinement
  console.log(testIfElseRefinement("hello")); // Should work
  console.log(testIfElseRefinement(null)); // Should work

  console.log(testTernaryRefinement("world")); // Should work after fix
  console.log(testTernaryRefinement(null)); // Should work after fix

  // Test nested ternary
  console.log(testNestedTernary("test", 42)); // Should work after fix
  console.log(testNestedTernary("test", null)); // Should work after fix
  console.log(testNestedTernary(null, 42)); // Should work after fix

  // Test typeof refinement
  console.log(testTernaryWithTypeOf("hello")); // Should work after fix
  console.log(testTernaryWithTypeOf(123)); // Should work after fix

  // Test instanceof refinement
  let arr: Array<string> = new Array<string>();
  arr.push("test");
  console.log(testTernaryWithInstanceOf(arr)); // Should work after fix
  console.log(testTernaryWithInstanceOf("str")); // Should work after fix

  // Test ADT refinement
  let successResponse: Response = { kind: "success", data: "success!" };
  let errorResponse: Response = { kind: "error", message: "error!" };

  console.log(testTernaryWithADT(successResponse)); // Should work after fix
  console.log(testTernaryWithADT(errorResponse)); // Should work after fix

  console.log("Ternary refinement tests completed!");
}

export {
  testIfElseRefinement,
  testTernaryRefinement,
  testNestedTernary,
  testTernaryWithTypeOf,
  testTernaryWithInstanceOf,
  testTernaryWithADT,
};
