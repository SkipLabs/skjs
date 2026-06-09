// Test type errors in try/catch blocks
function validTryCatch(): void {
  try {
    throw new Error("test");
  } catch (e) {
    console.log(e);
  }
}

function invalidReturnInFinally(): number {
  try {
    return 1;
  } finally {
    // @skjs-expect-error Type of returned value is not assignable to the function's return type
    return "invalid";
  }
}
